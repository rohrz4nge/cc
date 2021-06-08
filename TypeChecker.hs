module TypeChecker where

import AbsCPP
import PrintCPP
import ErrM

import qualified Data.Map as Map


type Context = Map.Map Id Type            -- variables with their types

type Sig = Map.Map Id ([Type], Type)      -- function type signature

type Env = (Sig, [Context], Structs)      -- functions and context stack

type Structs = Map.Map Id Struct          -- structs

type Struct = Map.Map Id (Integer, Type)  -- fields of struct. ("fields" war schon vorher definiert)

--------------------------------------------------------------
--------------------------------------------------------------

{-
typecheck nimmt den Syntax Tree vom Output des Parsers.
Zuerst werden alle Signaturen ins Environment eingefügt und anschließend
alle Funktionen ge-typechecked.
-}
typecheck :: Program -> Err (Program, Structs)
typecheck (PDefs defs1) = do
                          newEnv <- insertSignaturesIntoEnv defs1 emptyEnv
                          (envs, defs2) <- checkFunctions defs1 newEnv
                          structs <- giveBackStructs envs
                          return (PDefs defs2, structs)

--------------------------------------------------------------
--------------------------------------------------------------

giveBackStructs :: Env -> Err Structs
giveBackStructs (_ , _ , structs) = return structs

--Fügt Liste von Definitionen in Env ein
insertSignaturesIntoEnv :: [Def] -> Env -> Err Env
insertSignaturesIntoEnv [] env = return env
-- Funktion: gibt eine einzelne Funktions-Definition rekursiv an nächste Funktion weiter
insertSignaturesIntoEnv ((DFun typ id arguments statements):rest) env = do
                                                                          checkArguments arguments
                                                                          newEnv <- insertSignatureIntoEnv env id (getArgTypes arguments, typ)
                                                                          insertSignaturesIntoEnv rest newEnv
                                                                            where checkArguments ((ADecl argType id):args) = if argType == Type_void then Bad ("Void in args") else checkArguments args
                                                                                  checkArguments [] = Ok "jej"

-- Struct: gibt eine einzelne Struct-Definition rekursiv an nächste Funktion weiter
insertSignaturesIntoEnv ((DStruct id fields):rest) env                = do
                                                                          if checkStructConflict env fields
                                                                            then Bad ("Struct not defined")
                                                                            else do
                                                                              newEnv <- insertFieldIntoEnv env id fields
                                                                              insertSignaturesIntoEnv rest newEnv

checkStructConflict :: Env -> [Field] -> Bool
checkStructConflict _ [] = False
checkStructConflict env@(_, _, structs) ((FDecl ftype _):rest) = case ftype of
                                                (TypeId id) -> if Map.member id structs then checkStructConflict env rest else True
                                                _ -> checkStructConflict env rest

--Fügt einzelne Funktions-Definition in Env ein
insertSignatureIntoEnv :: Env -> Id -> ([Type], Type) -> Err Env
insertSignatureIntoEnv env@(signature, context, structs) id typ  = case lookFun env id of
                                                                    Bad _ -> return (Map.insert id typ signature, context, structs)
                                                                    Ok  _ -> Bad ("Function " ++ show id ++ " defined more than once.")

{-
Fügt einzelne Struct-Definition in Env ein
-}
insertFieldIntoEnv :: Env -> Id -> [Field] -> Err Env
insertFieldIntoEnv env@(signature, context, structs) id fields = do
                                                                    flds <- insertFields Map.empty (zip [0..] fields)
                                                                    if (Map.member id structs) then Bad ("Struct " ++ show id ++ " defined more than once.")
                                                                    else return (signature, context, Map.insert id flds structs)

{-
Fügt Felder in Struct ein
-}
insertFields :: Struct -> [(Integer, Field)] -> Err Struct
insertFields struct [] = return struct
insertFields struct ((int, FDecl typ id):rest) = case Map.insertLookupWithKey fun id (int, typ) struct of
                                                          (Nothing, newStruct) -> insertFields newStruct rest >>= return
                                                          (Just _, _) -> Bad ("Field " ++ show id ++ " already defined")
                                                          where fun id1 fld str = fld

{-
Gibt Typen der Argumente einer Funktion zurück
-}
getArgTypes :: [Arg] -> [Type]
getArgTypes []                  = []
getArgTypes (ADecl typ id:rest) = typ : (getArgTypes rest)

--------------------------------------------------------------

{-
Bekommt Liste von Definitionen und ruft rekursiv, für checkFuntion, jede einzelne mit einem neuen Block im Environment auf
-}
checkFunctions :: [Def] -> Env -> Err (Env, [Def])
checkFunctions [] env                 = return (env, [])
checkFunctions (definition:rest) env = do
                                        (newEnv, annotatedDef) <- checkFunction (newBlock env) definition
                                        (newEnv, annotatedDefs) <- checkFunctions rest newEnv
                                        return (newEnv, annotatedDef : annotatedDefs)

{-
Übergibt alle Argumente/Fields und alle Statements an zwei Funktionen
-}
checkFunction :: Env -> Def -> Err (Env, Def)
checkFunction env def@(DFun typ id arguments statements) = do
                                                              newEnv <- insertArguments arguments env
                                                              (newEnv, stms) <- checkStatements statements typ newEnv
                                                              return (newEnv, DFun typ id arguments stms)
checkFunction env def@(DStruct id fields) = do
                                              return (env, def)

{-
Jedes Argument wird rekursiv einzeln ins Env eingefügt, wenn noch nicht vorhanden
-}
insertArguments :: [Arg] -> Env -> Err Env
insertArguments [] env                  = return env
insertArguments (ADecl typ id:rest) env = updateVar id typ env >>= insertArguments rest

--------------------------------------------------------------

{-
Schaut, ob eine Variable im Context ist. Wenn vorhanden, dann returne den Typ der Variable
-}
lookVar :: Env -> Id -> Err Type
lookVar (x, [], structs) id           = Bad ("Variable " ++ show id ++ " not defined.")
lookVar (x, context:rest, structs) id | Map.member id context = return (context Map.! id)
                                      | otherwise = lookVar (x, rest, structs) id -- rekursiv im Context schauen


{-
Wie oben, returned aber die Typen in der Signatur der Funktion
-}
lookFun :: Env -> Id -> Err ([Type], Type)
lookFun (signatures, _, structs) id   | Map.member id signatures = return (signatures Map.! id)
                                      | otherwise = Bad ("Function " ++ show id ++ " not defined.")


lookField :: Env -> Id -> Type -> Err Type
lookField (_ , _, structs) structField (TypeId structId) = case Map.lookup structId structs of
                                                                Nothing -> Bad ("Struct " ++ show structId ++ " not defined.")
                                                                Just struct -> case Map.lookup structField struct of
                                                                                Nothing -> Bad ("Struct field " ++ show structField ++ " from struct " ++ show structId ++ " not defined.")
                                                                                Just (_, field) -> return field
lookField _ _ _ = Bad ("Variable cant be treated as struct")

--------------------------------------------------------------

{-
Initialisieren von einem leeren Environment
-}
emptyEnv  :: Env
emptyEnv = (Map.fromList [], [], Map.empty)

{-
Setze neuen Scope auf den Stack des Contexts
-}
newBlock  :: Env -> Env
newBlock (signatures, context, structs) = (signatures, Map.empty:context, structs)

popBlock :: Env -> Err Env
popBlock (_, [], _) = Bad ("Empty env")
popBlock (signatures, context, structs) = return (signatures, tail context, structs)

--------------------------------------------------------------

{-
Nimmt Liste von Statements und führt diese rekursiv in der nächsten Funktion aus
-}
checkStatements :: [Stm] -> Type -> Env -> Err (Env, [Stm])
checkStatements [] _ env                  = return (env, [])
checkStatements [statement] typ env       = do
                                              (newEnv, annotatedStm) <- checkStatement env statement typ
                                              return (newEnv, [annotatedStm])
checkStatements (statement:rest) typ env  = do
                                              (newEnv, annotatedStm) <- checkStatement env statement typ
                                              (newEnv, annotatedStms) <- checkStatements rest typ newEnv
                                              return (newEnv, annotatedStm : annotatedStms)


{-
Jede möglichen, der in der Grammar vorhandenen, Statements werden mit unterschiedlichen Funktionen gecheckt
-}
checkStatement :: Env -> Stm -> Type -> Err (Env, Stm)
checkStatement env@(signatures, context, structs) stm typ = case stm of
  -- x;
  SExp exp -> do
    (typ, annotatedExp) <- inferExp env exp         -- inferExp gibt Typen der Expression zurück
    return (env, (SExp annotatedExp))

  -- int x;
  SDecls typ1 ids -> do
    if (typ1 == Type_void)
      then Bad ("Cant declare var of type void")
      else do
        (newEnv, updatedIds) <- updateVars ids typ1 env               -- fügt neue Deklarationen ins Env hinzu
        return (newEnv, (SDecls typ1 updatedIds))

  -- int x = 5;
  -- SInit typ2 id exp -> do
  --   annotatedExp <- checkExp env typ2 exp           -- checkExp prüft, ob 'int x' mit '5' übereinstimmt
  --   newEnv <- updateVar id typ2 env                 -- wenn übereinstimmt, füge Variable zu Env hinzu
  --   return (newEnv, (SInit typ2 id annotatedExp))

  -- return 1
  SReturn exp -> do
    annotatedExp <- checkExp env typ exp            -- prüfe, ob return-Typ mit Funktions-Typ übereinstimmt
    return (env, (SReturn annotatedExp))            -- int main -> return 1

  SReturnV -> do
    if typ /= Type_void then Bad ("Void doesnt return anything") else return (env, (SReturnV))

  -- while(1) {[Stm]}
  SWhile exp stm -> do
    annotatedExp <- checkExp env Type_bool exp      -- prüfe ob Bedingung e in while(e) ein Bool ist
    (_,annotatedStm) <- checkStatement env stm typ  -- Prüfe rekursiv jedes Statement im while-Block
    return (env, (SWhile annotatedExp annotatedStm))

  SDoWhile stm exp -> do
    annotatedExp <- checkExp env Type_bool exp
    (_,annotatedStm) <- checkStatement env stm typ
    return (env, (SDoWhile annotatedStm annotatedExp))

  SFor exp1 exp2 exp3 stm -> do
    annotatedExp2 <- checkExp env Type_bool exp2
    (_, annotatedExp1) <- inferExp env exp1
    (_, annotatedExp3) <- inferExp env exp3
    (_, annotatedStm) <- checkStatement env stm typ
    return (env, (SFor annotatedExp1 annotatedExp2 annotatedExp3 annotatedStm))

  -- { [stms] }
  SBlock stms -> do
    (newEnv, newStms) <- checkStatements stms typ (newBlock env)
    popEnv <- popBlock newEnv
    return (popEnv, (SBlock newStms)) -- prüfe rekursiv jedes Statement in einem Block

  -- if (exp) stm1 stm2
  SIfElse exp stm1 stm2 -> do
    annotatedExp <- checkExp env Type_bool exp -- prüfe Bedingung
    (_, annotatedStm1) <- checkStatement env stm1 typ -- checke Statements in if-Branch
    (_, annotatedStm2) <- checkStatement env stm2 typ -- und im else-Branch
    return (env, (SIfElse annotatedExp annotatedStm1 annotatedStm2))

{-
Prüft die Argumente bei einem Funktionsaufruf mit den Typen im Env und ob ausreichend Argumente vorhanden sind
-}
checkFunArguments :: Env -> Id -> [Type] -> [Exp] -> Err Env
checkFunArguments env id [] [] = return env
checkFunArguments env id types [] = Bad ("No expressions given.")
checkFunArguments env id [] exps = Bad ("No types given.")
checkFunArguments env id types@(typ:rest1) exps@(exp:rest2) = if (length types == length exps) then do
                                                                checkExp env typ exp
                                                                checkFunArguments env id rest1 rest2
                                                              else Bad ("Unequal amount of arguments and types.")

{-
Prüft, ob der Typ einer Expression mit einem angegebenen Typ übereinstimmt
-}
checkExp :: Env -> Type -> Exp -> Err Exp
checkExp env typ exp = do
                          (t, annotatedExp) <- inferExp env exp
                          convertType <- typeConversion t typ
                          if convertType == typ then return annotatedExp
                          else Bad ("Type o " ++ show typ ++ " and " ++ show convertType ++ " not equal.")

--------------------------------------------------------------

{-
Rekursiv updateVar aufrufen
-}
updateVars :: [IdIn] -> Type -> Env -> Err (Env, [IdIn])
updateVars [] typ env = return (env, [])
updateVars ((IdInit id exp):rest) typ env = do
  annotatedExp <- checkExp env typ exp
  newEnv <- updateVar id typ env
  (retEnv, remIds) <- updateVars rest typ newEnv
  return (retEnv, (IdInit id annotatedExp):remIds)
updateVars ((IdNoInit id):rest) typ env = do
  newEnv <- updateVar id typ env
  (retEnv, remIds) <- updateVars rest typ newEnv
  return (retEnv, (IdNoInit id):remIds)


{-
Prüft, ob eine Variable bereits vorhanden ist. Wenn nicht, dann füge in den Context hinzu
-}
updateVar :: Id -> Type -> Env -> Err Env
updateVar  id typ env@(signature, [], structs)            = updateVar id typ (newBlock env)
updateVar  id typ env@(signature, context:rest, structs)  = case Map.insertLookupWithKey fun id typ context of
                                                              (Nothing, context2) -> return (signature, context2:rest, structs)
                                                              (Just a, context3) -> Bad ("Variable " ++ show id ++ " already defined.")
                                                              where fun id1 typ1 context1 = typ1

--------------------------------------------------------------

checkForId :: Exp -> Bool
checkForId (EId _) = True
checkForId (EProj exp1 _) = checkForId exp1
checkForId _ = False

{-
Expression wird inferenziert (Typ wird herausgefunden)
-}
inferExp :: Env -> Exp -> Err (Type, Exp)
inferExp env exp = case exp of
  ETrue                   -> return   (Type_bool, ETyped ETrue Type_bool)
  EFalse                  -> return   (Type_bool, ETyped EFalse Type_bool)
  EInt int                -> return   (Type_int, ETyped (EInt int) Type_int)
  EDouble double          -> return   (Type_double, ETyped (EDouble double) Type_double)

  EId id                  -> do
                              typ <- lookVar env id
                              return (typ, ETyped (EId id) typ)

  EApp id exps            -> do
                              (argTypes, returnType) <- inferFun env id exps
                              aExprs <- mapM (\(expr, typ) -> checkExp env typ expr) (zip exps argTypes)
                              return (returnType, ETyped (EApp id aExprs) returnType)

  EProj exp1 id   -> do
                              (structTyp, annotatedExp) <- inferExp env exp1
                              fieldTyp <- lookField env id structTyp
                              return (fieldTyp, ETyped (EProj annotatedExp id) fieldTyp)

  EIncr exp1   -> do
                              if not (checkForId exp1)
                                then Bad ("Cant project on incr non variable")
                                else do
                                  (_, annotatedExp) <- inferExp env exp1
                                  typ <- inferUnaryExp exp1 env
                                  return (typ, ETyped (EIncr annotatedExp) typ)

  EDecr exp1   -> do
                              if not (checkForId exp1)
                                then Bad ("Cant project on incr non variable")
                                else do
                                  (_, annotatedExp) <- inferExp env exp1
                                  typ <- inferUnaryExp exp1 env
                                  return (typ, ETyped (EDecr annotatedExp) typ)

  EPIncr exp1   -> do
                              if not (checkForId exp1)
                                then Bad ("Cant project on incr non variable")
                                else do
                                  (_, annotatedExp) <- inferExp env exp1
                                  typ <- inferUnaryExp exp1 env
                                  return (typ, ETyped (EPIncr annotatedExp) typ)

  EPDecr exp1   -> do
                              if not (checkForId exp1)
                                then Bad ("Cant project on incr non variable")
                                else do
                                  (_, annotatedExp) <- inferExp env exp1
                                  typ <- inferUnaryExp exp1 env
                                  return (typ, ETyped (EPDecr annotatedExp) typ)

  ETimes  exp1 exp2       -> do
                              (typ, annotatedExp1, annotatedExp2) <- inferArithmExp exp1 exp2 env
                              return (typ, ETyped (ETimes annotatedExp1 annotatedExp2) typ)

  EDiv    exp1 exp2       -> do
                              (typ, annotatedExp1, annotatedExp2) <- inferArithmExp exp1 exp2 env
                              return (typ, ETyped (EDiv annotatedExp1 annotatedExp2) typ)

  EPlus   exp1 exp2       -> do
                              (typ, annotatedExp1, annotatedExp2) <- inferArithmExp exp1 exp2 env
                              return (typ, ETyped (EPlus annotatedExp1 annotatedExp2) typ)

  EMinus  exp1 exp2       -> do
                              (typ, annotatedExp1, annotatedExp2) <- inferArithmExp exp1 exp2 env
                              return (typ, ETyped (EMinus annotatedExp1 annotatedExp2) typ)

  EUPlus   exp1            -> do
                              (typ, annotatedExp1, annotatedExp2) <- inferArithmExp exp1 exp1 env
                              return (typ, ETyped (EUPlus annotatedExp1) typ)

  EUMinus  exp1            -> do
                              (typ, annotatedExp1, annotatedExp2) <- inferArithmExp exp1 exp1 env
                              return (typ, ETyped (EUMinus annotatedExp1) typ)

  ELt     exp1 exp2       -> do
                              typ <- inferOrderingsExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_bool, ETyped (ELt annotatedExp1 annotatedExp2) Type_bool)

  EGt     exp1 exp2       -> do
                              typ <- inferOrderingsExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_bool, ETyped (EGt annotatedExp1 annotatedExp2) Type_bool)

  ELtEq   exp1 exp2       -> do
                              typ <- inferOrderingsExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_bool, ETyped (ELtEq annotatedExp1 annotatedExp2) Type_bool)

  EGtEq   exp1 exp2       -> do
                              typ <- inferOrderingsExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_bool, ETyped (EGtEq annotatedExp1 annotatedExp2) Type_bool)

  EEq     exp1 exp2       -> do
                              (type1, annotatedExp1) <- inferExp env exp1
                              (type2, annotatedExp2) <- inferExp env exp2
                              if (type1 == Type_void || type2 == Type_void)
                                then Bad ("No void comparison")
                                else return (Type_bool, ETyped (EEq annotatedExp1 annotatedExp2) Type_bool)

  ENEq    exp1 exp2       -> do
                              (type1, annotatedExp1) <- inferExp env exp1
                              (type2, annotatedExp2) <- inferExp env exp2
                              if (type1 == Type_void || type2 == Type_void)
                                then Bad ("No void comparison")
                                else return (Type_bool, ETyped (ENEq annotatedExp1 annotatedExp2) Type_bool)

  EAnd    exp1 exp2       -> do
                              typ <- inferBoolExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_bool, ETyped (EAnd annotatedExp1 annotatedExp2) Type_bool)

  EOr     exp1 exp2       -> do
                              typ <- inferBoolExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_bool, ETyped (EOr annotatedExp1 annotatedExp2) Type_bool)

  EAss    exp1 exp2       -> do
                              if not (checkForId exp1)
                                then Bad ("Cant project on incr non variable")
                                else do
                                  typ <- inferAssignExp exp1 exp2 env
                                  (_, annotatedExp1) <- inferExp env exp1
                                  (_, annotatedExp2) <- inferExp env exp2
                                  return (typ, ETyped (EAss annotatedExp1 annotatedExp2) typ)

  ETwc     exp1 exp2       -> do
                              typ <- inferOrderingsExp exp1 exp2 env
                              (_, annotatedExp1) <- inferExp env exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              return (Type_int, ETyped (ETwc annotatedExp1 annotatedExp2) Type_int)

  ECond exp1 exp2 exp3     -> do
                              typ <- inferAssignExp exp2 exp3 env
                              annotatedExp1 <- checkExp env Type_bool exp1
                              (_, annotatedExp2) <- inferExp env exp2
                              (_, annotatedExp3) <- inferExp env exp3
                              return (typ, ETyped (ECond annotatedExp1 annotatedExp2 annotatedExp3) typ)


{-
Prüft, ob Funktion richtig aufgebaut ist und gibt anschließend den return-Type der Funktion zurück
-}
inferFun :: Env -> Id -> [Exp] -> Err ([Type], Type)
inferFun env id exps = lookFun env id >>= \(argumentTypes, returnType) -> checkFunArguments env id argumentTypes exps >> return (argumentTypes, returnType)

{-
Prüft, ob unäre Operatoren nur int oder double sind
i++, i--, ...
-}
inferUnaryExp :: Exp -> Env -> Err Type
inferUnaryExp exp env = inferExp env exp >>= \(typ, _) ->
  if elem typ [Type_int, Type_double] then return typ
  else Bad ("Expression " ++ show exp ++ " has wrong type.")

-- +, -, *, /
inferArithmExp :: Exp -> Exp -> Env -> Err (Type, Exp, Exp)
inferArithmExp exp1 exp2 env = do
                                  (typ1, aExp1) <- inferExp env exp1
                                  (typ2, aExp2) <- inferExp env exp2
                                  typ' <- inferExpsInTypes [Type_int, Type_double] typ1 typ2 env
                                  return (typ', aExp1, aExp2)


-- <, >, <=, >=
inferOrderingsExp :: Exp -> Exp -> Env -> Err Type
inferOrderingsExp = inferExpsInTypes2 [Type_int, Type_double]

-- ==, !=
inferComparisonExp :: Exp -> Exp -> Env -> Err Type
inferComparisonExp = inferExpsInTypes2 [Type_int, Type_double, Type_bool]

-- &&, ||
inferBoolExp :: Exp -> Exp -> Env -> Err Type
inferBoolExp = inferExpsInTypes2 [Type_bool]

-- =
inferAssignExp :: Exp -> Exp -> Env -> Err Type
inferAssignExp exp1 exp2 env = do
                                (typ, _) <- inferExp env exp1
                                checkExp env typ exp2
                                return typ

-- id.field = value
inferProjAssignExp :: Exp -> Exp -> Exp -> Env -> Err Type
inferProjAssignExp (EId structId) structField value env = do
                                                (typ1, _) <- inferExp env (EProj structField structId)
                                                (typ2, _) <- inferExp env value
                                                if (typ1 /= typ2) then
                                                  Bad ("Different struct types when assigning.")
                                                else return typ1

-- immer in den genaueren Typen konvertieren
typeConversion :: Type -> Type -> Err Type
typeConversion Type_int     Type_double = return Type_double
typeConversion Type_double  Type_int    = return Type_double
typeConversion x y = if x == y then return x else Bad ("Types " ++ show x ++ " and " ++ show y ++ " are not compatible with each other.")

-- Prüfe, ob zwei Expressions in die angegebenen Liste mit erwarteten Typen passen und konvertiere sie ggfs.
inferExpsInTypes :: [Type] -> Type -> Type -> Env -> Err Type
inferExpsInTypes types typ1 typ2 env = do
                                    if elem typ1 types then do
                                      if elem typ2 types then do
                                        typ' <- typeConversion typ1 typ2
                                        return (typ')
                                      else Bad (show typ2 ++ " is not in expected types.")
                                    else Bad (show typ1 ++ " is not in expected types.")

inferExpsInTypes2 :: [Type] -> Exp -> Exp -> Env -> Err Type
inferExpsInTypes2 types exp1 exp2 env = do
                                          (typ1, _) <- inferExp env exp1
                                          (typ2, _) <- inferExp env exp2
                                          inferExpsInTypes types typ1 typ2 env
