module Auss where

import CodeGen
import qualified AbsCPP as ABS
import TypeChecker
import Control.Monad.State as CMS
import Data.Word as W

import qualified Data.Map as Map

import Control.Monad.Except

import qualified LLVM.AST as L
import qualified LLVM.AST.Global as LGLOBAL
import qualified LLVM.AST.Linkage as LLINKAGE
import qualified LLVM.AST.CallingConvention as LCALLCONV
import qualified LLVM.AST.Attribute as LATTRIBUTE
import qualified LLVM.AST.Constant as LCONSTANT
import qualified LLVM.AST.Float as LFLOAT
import qualified LLVM.AST.FloatingPointPredicate as LFPP
import qualified LLVM.AST.IntegerPredicate as LINTPRED
import qualified LLVM.Module as LMOD
import qualified LLVM.Internal.Context as LINTC
import qualified LLVM.AST.AddrSpace as LADDR

import qualified Data.ByteString as DB
import qualified Data.ByteString.Char8 as CDB
--------------------------------------------------------------

liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

codegen :: L.Module -> ABS.Program -> Structs -> IO String
codegen mod (ABS.PDefs defs) structs = do
  programString <- LINTC.withContext (\context -> LMOD.withModuleFromAST context newast (\m -> LMOD.moduleLLVMAssembly m))
  return $ CDB.unpack programString
    where
      modn    = mapM (codegenTop structs argtyps) defs
      argtyps = argTypeMapInit defs
      newast  = runLLVM mod modn


standardValue :: ABS.Type -> Maybe L.Operand
standardValue ABS.Type_bool    = Just false
standardValue ABS.Type_int     = Just intConsZero
standardValue ABS.Type_double  = Just doubleConsZero
standardValue ABS.Type_void    = Nothing

typeconversion :: ABS.Type -> L.Type
typeconversion ABS.Type_void            = CodeGen.void
typeconversion ABS.Type_bool            = CodeGen.bool
typeconversion ABS.Type_int             = CodeGen.int
typeconversion ABS.Type_double          = CodeGen.double
typeconversion (ABS.TypeId (ABS.Id id)) = L.NamedTypeReference (name' id)


typeDconversion :: L.Operand -> Codegen (L.Operand)
typeDconversion operand@(L.LocalReference (L.IntegerType _) _)  = sitofp operand
typeDconversion operand@(L.ConstantOperand (LCONSTANT.Int _ _)) = sitofp operand
typeDconversion operand                                         = return operand

-- converttype :: L.Operand -> ABS.Type -> Codegen (L.Operand)
-- converttype operand@(L.LocalReference (L.IntegerType _) _) ABS.Type_double = uitofp operand
-- converttype operand@(L.ConstantOperand (LCONSTANT.Int _ _)) ABS.Type_double = uitofp operand
-- converttype operand _ = return operand

typeCast :: L.Operand -> ABS.Type -> ABS.Type -> Codegen (L.Operand)
typeCast operand ABS.Type_int ABS.Type_double = sitofp operand
typeCast operand _ _ = return operand


-------------------------------------------------------------

argTypeMapInit :: [ABS.Def] -> Map.Map L.Name [ABS.Type]
argTypeMapInit [] = Map.empty
argTypeMapInit ((ABS.DFun rettyp (ABS.Id id) arguments statements):rest) = Map.insert (name' id) (map (\(ABS.ADecl typ id2) -> typ) arguments) (argTypeMapInit rest)
argTypeMapInit (_:rest) = argTypeMapInit rest

lookFieldIndex :: Structs -> ABS.Id -> ABS.Id -> Integer
lookFieldIndex structs structId structField = case Map.lookup structId structs of
                                                Nothing -> error ("Struct " ++ show structId ++ " not defined.")
                                                Just struct -> case Map.lookup structField struct of
                                                                  Just (fieldId, _) -> fieldId
                                                                  Nothing -> error ("Struct field " ++ show structField ++ " from struct " ++ show structId ++ " not defined.")

getStructIndex :: Structs -> ABS.Id -> ABS.Id -> [L.Operand]
getStructIndex structs structId structField = [intConsZero, cons $ LCONSTANT.Int 32 (lookFieldIndex structs structId structField)]


getStructField :: L.Operand -> ABS.Type -> Integer -> Codegen L.Operand
getStructField struct stype index = extractStructFieldValue (typeconversion stype) struct [(fromIntegral index)]


getStructPos :: ABS.Exp -> ABS.Id -> ABS.Type -> Codegen L.Operand
getStructPos exp fieldId typ = case exp of
  (ABS.ETyped (ABS.EId (ABS.Id structvarid)) (ABS.TypeId structtype))         -> do
                                                                                  structs <- getStructs
                                                                                  var <- getvar structvarid
                                                                                  getElementPtr var (getStructIndex structs structtype fieldId) (typeconversion typ)
  (ABS.ETyped (ABS.EProj struct memberid) (ABS.TypeId structtype))  -> do
                                                                                  structs <- getStructs
                                                                                  position <- getStructPos struct memberid typ
                                                                                  getElementPtr position (getStructIndex structs structtype fieldId) (typeconversion typ)


getStructVar :: ABS.Exp -> ABS.Id -> ABS.Type -> Codegen L.Operand
getStructVar exp fieldId typ = do
                                  operand <- genExpression exp
                                  structs <- getStructs
                                  case (extractType exp) of
                                     (ABS.TypeId id) -> getStructField operand typ (lookFieldIndex structs id fieldId)

--------------------------------------------------------------


codegenTop :: Structs -> Map.Map L.Name [ABS.Type] -> ABS.Def -> LLVM ()
codegenTop structs argtyps (ABS.DFun typ (ABS.Id id) arguments statements) = define (typeconversion typ) id (fnArgs arguments) bls
  where
    bls = createBlocks $ execCodegen [] structs argtyps $ do
      entryName <- addBlock entryBlockName
      setBlock entryName
      forM arguments $ \(ABS.ADecl typ' (ABS.Id id')) -> do
        var <- alloca (typeconversion typ')
        store var (local (name' id') (typeconversion typ'))
        assign id' var
      genStatements statements
      case typ of
        typeId@(ABS.TypeId id) -> do
          retStruct <- alloca (typeconversion typeId)
          operand <- load retStruct
          ret (Just operand)
        _ -> ret (standardValue typ)
codegenTop _ _ (ABS.DStruct (ABS.Id id) fields) = structDefine id (fnFields fields)


fnArgs :: [ABS.Arg] -> [(L.Type, L.Name)]
fnArgs [] = []
fnArgs ((ABS.ADecl argTyp (ABS.Id argId)):rest) = (typeconversion argTyp, name' argId) : fnArgs rest

fnFields :: [ABS.Field] -> [L.Type]
fnFields [] = []
fnFields ((ABS.FDecl fieldTyp _):rest) = (typeconversion fieldTyp) : fnFields rest

toPointer :: L.Type -> [L.Type] -> L.Type
toPointer funTyp argTyps = L.PointerType {L.pointerReferent = (L.FunctionType funTyp argTyps False), L.pointerAddrSpace = LADDR.AddrSpace 0}

extractType :: ABS.Exp -> ABS.Type
extractType (ABS.ETyped _ typ) = typ

genStatements :: [ABS.Stm] -> Codegen ()
genStatements [] = return()
genStatements (stm:rest) = do
                              genStatement stm
                              genStatements rest

genStatement :: ABS.Stm -> Codegen ()
genStatement stm = case stm of
  (ABS.SReturn exp) -> do
                          expCode <- genExpression exp
                          ret (Just expCode)
                          return ()

  (ABS.SReturnV) -> do
                          ret (Nothing)
                          return ()

  (ABS.SDecls typ ids) -> forM_ ids helper
    where helper (ABS.IdInit (ABS.Id id) exp) = do
            var <- alloca (typeconversion typ)
            op <- genExpression exp
            convop <- typeCast op (extractType exp) typ
            store var convop
            assign id var
          helper (ABS.IdNoInit (ABS.Id id)) = do
            var <- alloca (typeconversion typ)
            assign id var

  (ABS.SExp exp) -> do
                      genExpression exp
                      return ()

  (ABS.SBlock stms) -> do
                          symtable <- getsymtab
                          genStatements stms
                          restoresymtab symtable


  (ABS.SIfElse exp stm1 stm2) -> do
                                    ifthen <- addBlock "if.then"
                                    ifelse <- addBlock "if.else"
                                    ifexit <- addBlock "if.exit"
                                    cond <- genExpression exp
                                    cbr cond ifthen ifelse
                                    setBlock ifthen
                                    ifBranch <- genStatement stm1
                                    br ifexit
                                    setBlock ifelse
                                    elseBranch <- genStatement stm2
                                    br ifexit
                                    setBlock ifexit
                                    return ()

  (ABS.SWhile exp stm) -> do
                            whileEntry <- addBlock "while.entry"
                            whileLoop <- addBlock "while.loop"
                            whileExit <- addBlock "while.exit"
                            br whileEntry
                            setBlock whileEntry
                            cond <- genExpression exp
                            cbr cond whileLoop whileExit
                            setBlock whileLoop
                            genStatement stm
                            br whileEntry
                            setBlock whileExit
                            return ()

  (ABS.SDoWhile stm exp) -> do
                            doWhileLoop <- addBlock "doWhile.loop"
                            doWhileCond <- addBlock "doWhile.cond"
                            doWhileExit <- addBlock "doWhile.exit"
                            br doWhileLoop
                            setBlock doWhileLoop
                            genStatement stm
                            br doWhileCond
                            setBlock doWhileCond
                            cond <- genExpression exp
                            cbr cond doWhileLoop doWhileExit
                            setBlock doWhileExit
                            return ()

  (ABS.SFor exp1 exp2 exp3 stm) -> do
    forCond <- addBlock "for.cond"
    forLoop <- addBlock "for.loop"
    forExit <- addBlock "for.exit"
    genExpression exp1
    br forCond
    setBlock forCond
    cond <- genExpression exp2
    cbr cond forLoop forExit
    setBlock forLoop
    genStatement stm
    genExpression exp3
    br forCond
    setBlock forExit
    return()

compareTypes :: ABS.Type -> ABS.Type -> (Bool, ABS.Type)
compareTypes ABS.Type_int ABS.Type_double = (True, ABS.Type_double)
compareTypes ABS.Type_double ABS.Type_int = (True, ABS.Type_double)
compareTypes typ1 typ2 = if (typ1 == typ2) then (True, typ1) else (False, ABS.Type_void)


compareOperands :: L.Operand -> L.Operand -> ABS.Type -> Codegen L.Operand
compareOperands lOperand rOperand ABS.Type_int = icmp LINTPRED.EQ lOperand rOperand
compareOperands lOperand rOperand ABS.Type_bool = icmp LINTPRED.EQ lOperand rOperand
compareOperands lOperand rOperand ABS.Type_double = fcmp LFPP.OEQ lOperand rOperand
compareOperands lOperand rOperand (ABS.TypeId id) = deepCompareStructs lOperand rOperand id


compareFields :: L.Operand -> L.Operand -> (Integer, ABS.Type) -> Codegen L.Operand
compareFields lop rop (index, typ) = do
  fieldOpL <- getStructField lop typ index
  fieldOpR <- getStructField rop typ index
  compareOperands fieldOpL fieldOpR typ


deepCompareStructs :: L.Operand -> L.Operand -> ABS.Id -> Codegen L.Operand
deepCompareStructs lop rop id = do
                                  structs <- getStructs
                                  currStruct <- case Map.lookup id structs of
                                                        Just s -> return s
                                                        Nothing -> error ("Couldnt find struct")
                                  let fields = Map.elems currStruct
                                  boolList <- mapM (\f -> compareFields lop rop f) fields
                                  foldM (\acc b -> band acc b) true boolList

genExpression :: ABS.Exp -> Codegen L.Operand
genExpression exp = case exp of
  (ABS.ETyped ABS.ETrue _)  -> return true
  (ABS.ETyped ABS.EFalse _) -> return false
  (ABS.ETyped (ABS.EInt int) _)          -> return (cons (LCONSTANT.Int 32 int))
  (ABS.ETyped (ABS.EDouble double) _)    -> return (cons (LCONSTANT.Float (LFLOAT.Double double)))

  (ABS.ETyped (ABS.EId (ABS.Id id)) _) -> do
                                            var <- getvar id
                                            load var

  -- Function arguments generated and function called
  (ABS.ETyped (ABS.EApp (ABS.Id id) argexps) typ) -> do
                                                      argcodes <- mapM genExpression argexps
                                                      argMap <- CMS.gets argTypes
                                                      let argTyps = case Map.lookup (name' id) argMap of
                                                                         Just types -> types
                                                                         Nothing -> error ("Failed Function lookup")
                                                      argOps <- mapM (\(ac, at, ae) -> (typeCast ac (extractType ae) at)) (zip3 argcodes argTyps argexps)
                                                      let totalType = toPointer (typeconversion typ) (map typeconversion argTyps)
                                                      case typ of
                                                        ABS.Type_void -> do callVoid (externf (name' id) totalType) argOps
                                                                            return intConsZero
                                                        _ -> call (externf (name' id) totalType) argOps (typeconversion typ)


  -- load field
  (ABS.ETyped (ABS.EProj exp1 (ABS.Id fieldId)) fieldTyp) -> getStructVar exp1 (ABS.Id fieldId) fieldTyp

  -- Increase integer or double prefix: ++i
  (ABS.ETyped (ABS.EPIncr (ABS.ETyped (ABS.EId (ABS.Id id)) _)) typ) -> do
                                                                          var <- getvar id
                                                                          operand <- load var
                                                                          case typ of
                                                                            --Increasing an integer
                                                                            ABS.Type_int -> do
                                                                              iaddresult <- iadd operand intConsOne
                                                                              store var iaddresult
                                                                              return operand
                                                                            --Increasing a double
                                                                            ABS.Type_double -> do
                                                                              faddresult <- fadd operand doubleConsOne
                                                                              store var faddresult
                                                                              return operand

  (ABS.ETyped (ABS.EPIncr (ABS.ETyped (ABS.EProj exp1 (ABS.Id structFieldId)) _)) structFieldTyp) -> do
                                                                        position <- getStructPos exp1 (ABS.Id structFieldId) structFieldTyp
                                                                        operand <- load position
                                                                        case structFieldTyp of
                                                                          ABS.Type_int -> do
                                                                            iaddresult <- iadd operand intConsOne
                                                                            store position iaddresult
                                                                            return operand
                                                                          ABS.Type_double -> do
                                                                            faddresult <- fadd operand doubleConsOne
                                                                            store position faddresult
                                                                            return operand

  -- Decrease integer or double prefix: --i
  (ABS.ETyped (ABS.EPDecr (ABS.ETyped (ABS.EId (ABS.Id id)) _)) typ) -> do
                                                                          var <- getvar id
                                                                          operand <- load var
                                                                          case typ of
                                                                            --Decreasing an integer
                                                                            ABS.Type_int -> do
                                                                              isubresult <- isub operand intConsOne
                                                                              store var isubresult
                                                                              return operand
                                                                            --Decreasing a double
                                                                            ABS.Type_double -> do
                                                                              fsubresult <- fsub operand doubleConsOne
                                                                              store var fsubresult
                                                                              return operand

  (ABS.ETyped (ABS.EPDecr (ABS.ETyped (ABS.EProj exp1 (ABS.Id structFieldId)) _)) structFieldTyp) -> do
                                                                        position <- getStructPos exp1 (ABS.Id structFieldId) structFieldTyp
                                                                        operand <- load position
                                                                        case structFieldTyp of
                                                                          ABS.Type_int -> do
                                                                            isubresult <- isub operand intConsOne
                                                                            store position isubresult
                                                                            return operand
                                                                          ABS.Type_double -> do
                                                                            fsubresult <- fsub operand doubleConsOne
                                                                            store position fsubresult
                                                                            return operand

  -- Increase integer or double postfix: i++
  (ABS.ETyped (ABS.EIncr (ABS.ETyped (ABS.EId (ABS.Id id)) _)) typ) -> do
                                                                          var <- getvar id
                                                                          operand <- load var
                                                                          case typ of
                                                                              ABS.Type_int -> do
                                                                                              iaddresult <- iadd operand intConsOne
                                                                                              store var iaddresult
                                                                                              return iaddresult
                                                                              ABS.Type_double -> do
                                                                                                  iaddresult <- fadd operand doubleConsOne
                                                                                                  store var iaddresult
                                                                                                  return iaddresult

  (ABS.ETyped (ABS.EIncr (ABS.ETyped (ABS.EProj exp1 (ABS.Id structFieldId)) _)) structFieldTyp) -> do
                                                                        position <- getStructPos exp1 (ABS.Id structFieldId) structFieldTyp
                                                                        operand <- load position
                                                                        case structFieldTyp of
                                                                          ABS.Type_int -> do
                                                                            iaddresult <- iadd operand intConsOne
                                                                            store position iaddresult
                                                                            return iaddresult
                                                                          ABS.Type_double -> do
                                                                            faddresult <- fadd operand doubleConsOne
                                                                            store position faddresult
                                                                            return faddresult

  -- Decrease integer or double postfix: i--
  (ABS.ETyped (ABS.EDecr (ABS.ETyped (ABS.EId (ABS.Id id)) _)) typ) -> do
                                                                          var <- getvar id
                                                                          operand <- load var
                                                                          case typ of
                                                                            ABS.Type_int -> do
                                                                                            isubresult <- isub operand intConsOne
                                                                                            store var isubresult
                                                                                            return isubresult
                                                                            ABS.Type_double -> do
                                                                                            fsubresult <- fsub operand doubleConsOne
                                                                                            store var fsubresult
                                                                                            return fsubresult

  (ABS.ETyped (ABS.EDecr (ABS.ETyped (ABS.EProj exp1 (ABS.Id structFieldId)) _)) structFieldTyp) -> do
                                                                        position <- getStructPos exp1 (ABS.Id structFieldId) structFieldTyp
                                                                        operand <- load position
                                                                        case structFieldTyp of
                                                                          ABS.Type_int -> do
                                                                            isubresult <- isub operand intConsOne
                                                                            store position isubresult
                                                                            return isubresult
                                                                          ABS.Type_double -> do
                                                                            fsubresult <- fsub operand doubleConsOne
                                                                            store position fsubresult
                                                                            return fsubresult
  -- a * b
  (ABS.ETyped (ABS.ETimes exp1 exp2) typ) -> do
                                              gen1 <- genExpression exp1
                                              gen2 <- genExpression exp2
                                              resultType1 <- typeCast gen1 (extractType exp1) (extractType exp2)
                                              resultType2 <- typeCast gen2 (extractType exp2) (extractType exp1)
                                              case typ of
                                                ABS.Type_int -> imul resultType1 resultType2
                                                ABS.Type_double -> fmul resultType1 resultType2

  (ABS.ETyped (ABS.ECond exp1 exp2 exp3) typ) -> do
                                              left <- addBlock "cond.left"
                                              right <- addBlock "cond.right"
                                              exit <- addBlock "cond.exit"
                                              condOp <- genExpression exp1
                                              cbr condOp left right
                                              setBlock left
                                              resultLeft <- genExpression exp2
                                              br exit
                                              setBlock right
                                              resultRight <- genExpression exp3
                                              br exit
                                              setBlock exit
                                              phi (typeconversion typ) [(resultLeft, left), (resultRight, right)]

  -- a / b
  (ABS.ETyped (ABS.EDiv exp1 exp2) typ) -> do
                                            gen1 <- genExpression exp1
                                            gen2 <- genExpression exp2
                                            resultType1 <- typeCast gen1 (extractType exp1) (extractType exp2)
                                            resultType2 <- typeCast gen2 (extractType exp2) (extractType exp1)
                                            case typ of
                                              ABS.Type_int -> idiv resultType1 resultType2
                                              ABS.Type_double -> fdiv resultType1 resultType2

  -- a + b
  (ABS.ETyped (ABS.EPlus exp1 exp2) typ) -> do
                                              gen1 <- genExpression exp1
                                              gen2 <- genExpression exp2
                                              resultType1 <- typeCast gen1 (extractType exp1) (extractType exp2)
                                              resultType2 <- typeCast gen2 (extractType exp2) (extractType exp1)
                                              case typ of
                                                ABS.Type_int -> iadd resultType1 resultType2
                                                ABS.Type_double -> fadd resultType1 resultType2

  -- a - b
  (ABS.ETyped (ABS.EMinus exp1 exp2) typ) -> do
                                              gen1 <- genExpression exp1
                                              gen2 <- genExpression exp2
                                              resultType1 <- typeCast gen1 (extractType exp1) (extractType exp2)
                                              resultType2 <- typeCast gen2 (extractType exp2) (extractType exp1)
                                              case typ of
                                                ABS.Type_int -> isub resultType1 resultType2
                                                ABS.Type_double -> fsub resultType1 resultType2

  (ABS.ETyped (ABS.EUPlus exp1) typ) -> do
                                              genExpression exp1

  (ABS.ETyped (ABS.EUMinus exp1) typ) -> do
                                              gen1 <- genExpression exp1
                                              case typ of
                                                ABS.Type_int -> isub intConsZero gen1
                                                ABS.Type_double -> fsub doubleConsZero gen1

  (ABS.ETyped (ABS.ETwc exp1 exp2) typ) -> do
                                              twcCondEq <- addBlock "twc.condGt"
                                              twcCondLt <- addBlock "twc.condLt"
                                              twcLeft <- addBlock "twc.left"
                                              twcRight <- addBlock "twc.right"
                                              twcExit <- addBlock "twc.exit"
                                              op1 <- genExpression exp1
                                              op2 <- genExpression exp2
                                              convOp1 <- typeDconversion op1
                                              convOp2 <- typeDconversion op2
                                              gtOp <- fcmp LFPP.OEQ convOp1 convOp2
                                              cbr gtOp twcCondEq twcCondLt
                                              setBlock twcCondEq
                                              let eqSuccess = intConsZero
                                              br twcExit
                                              setBlock twcCondLt
                                              ltOp <- fcmp LFPP.OLT convOp1 convOp2
                                              cbr ltOp twcLeft twcRight
                                              setBlock twcLeft
                                              let ltSuccess = intConsNegOne
                                              br twcExit
                                              setBlock twcRight
                                              let gtSuccess = intConsOne
                                              br twcExit
                                              setBlock twcExit
                                              phi int [(eqSuccess, twcCondEq), (ltSuccess, twcLeft), (gtSuccess, twcRight)]

  -- a < b
  (ABS.ETyped (ABS.ELt exp1 exp2) typ) -> do
                                            lOperand <- genExpression exp1
                                            rOperand <- genExpression exp2
                                            case (compareTypes (extractType exp1) (extractType exp2)) of
                                              (_, ABS.Type_int) -> icmp LINTPRED.SLT lOperand rOperand
                                              (_, ABS.Type_double) -> do
                                                                  lOperand' <- typeDconversion lOperand
                                                                  rOperand' <- typeDconversion rOperand
                                                                  fcmp LFPP.OLT lOperand' rOperand'

-- a > b
  (ABS.ETyped (ABS.EGt exp1 exp2) typ) -> do
                                            lOperand <- genExpression exp1
                                            rOperand <- genExpression exp2
                                            case (compareTypes (extractType exp1) (extractType exp2)) of
                                              (_, ABS.Type_int) -> icmp LINTPRED.SGT lOperand rOperand
                                              (_, ABS.Type_double) -> do
                                                                  lOperand' <- typeDconversion lOperand
                                                                  rOperand' <- typeDconversion rOperand
                                                                  fcmp LFPP.OGT lOperand' rOperand'

  -- a <= b
  (ABS.ETyped (ABS.ELtEq exp1 exp2) typ) -> do
                                              lOperand <- genExpression exp1
                                              rOperand <- genExpression exp2
                                              case (compareTypes (extractType exp1) (extractType exp2)) of
                                                (_, ABS.Type_int) -> icmp LINTPRED.SLE lOperand rOperand
                                                (_, ABS.Type_double) -> do
                                                                    lOperand' <- typeDconversion lOperand
                                                                    rOperand' <- typeDconversion rOperand
                                                                    fcmp LFPP.OLE lOperand' rOperand'

  -- a >= b
  (ABS.ETyped (ABS.EGtEq exp1 exp2) typ) -> do
                                              lOperand <- genExpression exp1
                                              rOperand <- genExpression exp2
                                              case (compareTypes (extractType exp1) (extractType exp2)) of
                                                (_, ABS.Type_int) -> icmp LINTPRED.SGE lOperand rOperand
                                                (_, ABS.Type_double) -> do
                                                                    lOperand' <- typeDconversion lOperand
                                                                    rOperand' <- typeDconversion rOperand
                                                                    fcmp LFPP.OGE lOperand' rOperand'

  -- a == b
  (ABS.ETyped (ABS.EEq exp1 exp2) typ) -> do
                                            lOperand <- genExpression exp1
                                            rOperand <- genExpression exp2
                                            let (isValid, eType) = compareTypes (extractType exp1) (extractType exp2)
                                            if isValid
                                              then do
                                                lNewOp <- typeCast lOperand (extractType exp1) eType
                                                rNewOp <- typeCast rOperand (extractType exp2) eType
                                                compareOperands lNewOp rNewOp eType
                                              else return false

  -- a != b
  (ABS.ETyped (ABS.ENEq exp1 exp2) typ) -> do
                                              lOperand <- genExpression exp1
                                              rOperand <- genExpression exp2
                                              let (isValid, eType) = compareTypes (extractType exp1) (extractType exp2)
                                              if isValid
                                                then do
                                                  lNewOp <- typeCast lOperand (extractType exp1) eType
                                                  rNewOp <- typeCast rOperand (extractType exp2) eType
                                                  equality <- compareOperands lNewOp rNewOp eType
                                                  icmp LINTPRED.EQ equality false
                                                else return true

  -- a && b
  (ABS.ETyped (ABS.EAnd exp1 exp2) _) -> do
                                          lOperand <- genExpression exp1
                                          rOperand <- genExpression exp2
                                          band lOperand rOperand
  -- a || b
  (ABS.ETyped (ABS.EOr exp1 exp2) _) -> do
                                          lOperand <- genExpression exp1
                                          rOperand <- genExpression exp2
                                          bor lOperand rOperand

  -- a = 5;
  (ABS.ETyped (ABS.EAss (ABS.ETyped (ABS.EId (ABS.Id id)) vartyp) exp2) _) -> do
                                                rOperand <- genExpression exp2
                                                convoperand <- typeCast rOperand (extractType exp2) vartyp
                                                var <- getvar id
                                                store var convoperand
                                                return convoperand

  (ABS.ETyped (ABS.EAss (ABS.ETyped (ABS.EProj exp1 (ABS.Id id)) vartyp) exp2) _) -> do
                                                rOperand <- genExpression exp2
                                                convoperand <- typeCast rOperand (extractType exp2) vartyp
                                                position <- getStructPos exp1 (ABS.Id id) vartyp
                                                store position convoperand
                                                return convoperand
