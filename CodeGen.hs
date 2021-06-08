{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CodeGen where

import TypeChecker
import AbsCPP as ABS
import qualified Data.Map as Map
import Control.Monad.State
import Data.List
import Data.Function
import Data.Word as W

import qualified LLVM.AST as L
import qualified LLVM.AST.Global as LGLOBAL

import LLVM.AST.Type hiding (double)
import qualified LLVM.AST.Float as LFLOAT
import qualified LLVM.AST.Linkage as LLINKAGE
import qualified LLVM.AST.Constant as LCONSTANT
import qualified LLVM.AST.Attribute as LATTRIBUTE
import qualified LLVM.AST.CallingConvention as LCALLCONV
import qualified LLVM.AST.IntegerPredicate as LINTPRED
import qualified LLVM.AST.FloatingPointPredicate as LFPP

import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Short hiding (lenght)

type Names = Map.Map String Int

type SymbolTable = [(String, L.Operand)]

---------------------------------------------------------------------------------
-- Types
---------------------------------------------------------------------------------

-- IEEE 754 double
double :: L.Type
double = L.FloatingPointType L.DoubleFP

doubleConsOne :: L.Operand
doubleConsOne = cons (LCONSTANT.Float (LFLOAT.Double 1))

doubleConsZero :: L.Operand
doubleConsZero = cons (LCONSTANT.Float (LFLOAT.Double 0))

int :: L.Type
int = L.IntegerType 32

intConsOne :: L.Operand
intConsOne = cons (LCONSTANT.Int 32 1)

intConsZero :: L.Operand
intConsZero = cons (LCONSTANT.Int 32 0)

intConsNegOne :: L.Operand
intConsNegOne = cons (LCONSTANT.Int 32 (-1))

void :: L.Type
void = L.VoidType

bool :: L.Type
bool = L.IntegerType 1

false :: L.Operand
false = cons (LCONSTANT.Int 1 0)

true :: L.Operand
true = cons (LCONSTANT.Int 1 1)

---------------------------------
-- Helper functions
---------------------------------

toShortByteString = toShort . BS.pack
toString = BS.unpack . fromShort

name' = L.Name . toShortByteString
label' = toShortByteString

---------------------------------------------------------------------------------
-- Code Generation Setup
---------------------------------------------------------------------------------

data CodegenState
  = CodegenState {
    currentBlock :: L.Name                      -- Name of the active block to append to
  , blocks       :: Map.Map L.Name BlockState   -- Blocks for function
  , argTypes     :: Map.Map L.Name [ABS.Type]   -- Argument types
  , symtab       :: SymbolTable                 -- Function scope symbol table
  , blockCount   :: Int                         -- Count of basic blocks
  , count        :: Word                        -- Count of unnamed instructions
  , names        :: Names                       -- Name Supply
  , allStructs   :: Structs
  } deriving Show


data BlockState
  = BlockState {
    idx   :: Int                                -- Block index
  , stack :: [L.Named L.Instruction]            -- Stack of instructions
  , term  :: Maybe (L.Named L.Terminator)       -- Block terminator
} deriving Show


newtype Codegen a = Codegen { runCodegen :: State CodegenState a }
  deriving (Functor, Applicative, Monad, MonadState CodegenState )


newtype LLVM a = LLVM (State L.Module a)
  deriving (Functor, Applicative, Monad, MonadState L.Module )


runLLVM :: L.Module -> LLVM a -> L.Module
runLLVM modul (LLVM m) = execState m modul


emptyModule :: String -> L.Module
emptyModule label = L.defaultModule { L.moduleName = (label' label) }


addDefn :: L.Definition -> LLVM ()
addDefn d = do
  defs <- gets L.moduleDefinitions
  modify $ \s -> s { L.moduleDefinitions = defs ++ [d] }


define ::  L.Type -> String -> [(L.Type, L.Name)] -> [L.BasicBlock] -> LLVM ()
define retty label argtys body = addDefn $
  L.GlobalDefinition $ L.functionDefaults {
    LGLOBAL.name        = name' label
  , LGLOBAL.parameters  = ([L.Parameter ty nm [] | (ty, nm) <- argtys], False)
  , LGLOBAL.returnType  = retty
  , LGLOBAL.basicBlocks = body
  }


external ::  L.Type -> String -> [(L.Type, L.Name)] -> LLVM ()
external retty label argtys = addDefn $
  L.GlobalDefinition $ L.functionDefaults {
    LGLOBAL.name        = name' label
  , LGLOBAL.linkage     = LLINKAGE.External
  , LGLOBAL.parameters  = ([L.Parameter ty nm [] | (ty, nm) <- argtys], False)
  , LGLOBAL.returnType  = retty
  , LGLOBAL.basicBlocks = []
  }

---------------------------------------------------------------------------------
-- Blocks
---------------------------------------------------------------------------------

entry :: Codegen L.Name
entry = gets currentBlock


addBlock :: String -> Codegen L.Name
addBlock bname = do
  bls <- gets blocks
  ix  <- gets blockCount
  nms <- gets names

  let new = emptyBlock ix
      (qname, supply) = uniqueName bname nms

  modify $ \s -> s { blocks = Map.insert (name' qname) new bls
                   , blockCount = ix + 1
                   , names = supply
                   }
  return (name' qname)


emptyBlock :: Int -> BlockState
emptyBlock i = BlockState i [] Nothing


setBlock :: L.Name -> Codegen L.Name
setBlock bname = do
  modify $ \s -> s { currentBlock = bname }
  return bname


getBlock :: Codegen L.Name
getBlock = gets currentBlock


getStructs :: Codegen Structs
getStructs = gets allStructs


modifyBlock :: BlockState -> Codegen ()
modifyBlock new = do
  active <- gets currentBlock
  modify (\s -> s { blocks = Map.insert active new (blocks s) })


current :: Codegen BlockState
current = do
  c <- gets currentBlock
  blks <- gets blocks
  case Map.lookup c blks of
    Just x -> return x
    Nothing -> error $ "no such block: " ++ show c


---------------------------------------------------------------------------------
-- Instructions
---------------------------------------------------------------------------------

fresh :: Codegen Word
fresh = do
  i <- gets count
  modify (\s -> s { count = 1 + i })
  return (i + 1)


uniqueName :: String -> Names -> (String, Names)
uniqueName nm ns =
  case Map.lookup nm ns of
    Nothing -> (nm,  Map.insert nm 1 ns)
    Just ix -> (nm ++ show ix, Map.insert nm (ix+1) ns)


---------------------------------------------------------------------------------
------ Referring to references of values ------
---------------------------------------------------------------------------------

local :: L.Name -> L.Type -> L.Operand
local name typ = L.LocalReference typ name


externf :: L.Name -> L.Type -> L.Operand
externf name typ = L.ConstantOperand $ LCONSTANT.GlobalReference typ name


---------------------------------------------------------------------------------
------ Symbol table as an association list ------
---------------------------------------------------------------------------------

assign :: String -> L.Operand -> Codegen ()
assign var x = do
  lcls <- gets symtab
  modify (\s -> s { symtab = (var, x) : lcls })


getvar :: String -> Codegen L.Operand
getvar var = do
  syms <- gets symtab
  case lookup var syms of
    Just x  -> return x
    Nothing -> error ("Local variable not in scope: " ++ show var)


---------------------------------------------------------------------------------
------ Push AST Note on current basic block stack ------
---------------------------------------------------------------------------------

instr :: L.Type -> L.Instruction -> Codegen L.Operand
instr typ ins = do
  n <- fresh
  let ref = (L.UnName n)
  blk <- current
  let i = stack blk
  modifyBlock (blk { stack = (ref L.:= ins) : i } )
  return (local ref typ)

unnamedInstr :: L.Instruction -> Codegen ()
unnamedInstr ins = do
  blk <- current
  let i = stack blk
  modifyBlock (blk { stack = (L.Do ins) : i})

instr_i :: L.Instruction -> Codegen L.Operand
instr_i instruct = instr CodeGen.int instruct


instr_d :: L.Instruction -> Codegen L.Operand
instr_d instruct = instr CodeGen.double instruct


instr_v :: L.Instruction -> Codegen L.Operand
instr_v instruct = instr CodeGen.void instruct


instr_b :: L.Instruction -> Codegen L.Operand
instr_b instruct = instr CodeGen.bool instruct


terminator :: L.Named L.Terminator -> Codegen (L.Named L.Terminator)
terminator trm = do
  blk <- current
  case term blk of
    Nothing -> do
      modifyBlock (blk { term = Just trm })
      return trm
    Just x -> return x


---------------------------------------------------------------------------------
------ Basic arithmetic operations ------
---------------------------------------------------------------------------------

fadd :: L.Operand -> L.Operand -> Codegen L.Operand
fadd a b = instr_d $ L.FAdd L.noFastMathFlags a b []

fsub :: L.Operand -> L.Operand -> Codegen L.Operand
fsub a b = instr_d $ L.FSub L.noFastMathFlags a b []

fmul :: L.Operand -> L.Operand -> Codegen L.Operand
fmul a b = instr_d $ L.FMul L.noFastMathFlags a b []

fdiv :: L.Operand -> L.Operand -> Codegen L.Operand
fdiv a b = instr_d $ L.FDiv L.noFastMathFlags a b []


iadd :: L.Operand -> L.Operand -> Codegen L.Operand
iadd a b = instr_i $ L.Add True False a b []

isub :: L.Operand -> L.Operand -> Codegen L.Operand
isub a b = instr_i $ L.Sub True False a b []

imul :: L.Operand -> L.Operand -> Codegen L.Operand
imul a b = instr_i $ L.Mul True False a b []

idiv :: L.Operand -> L.Operand -> Codegen L.Operand
idiv a b = instr_i $ L.SDiv False a b []


fcmp :: LFPP.FloatingPointPredicate -> L.Operand -> L.Operand -> Codegen L.Operand
fcmp cond a b = instr_d $ L.FCmp cond a b []

icmp :: LINTPRED.IntegerPredicate -> L.Operand -> L.Operand -> Codegen L.Operand
icmp cond a b = instr_i $ L.ICmp cond a b []

band :: L.Operand -> L.Operand -> Codegen L.Operand
band a b = instr_b $ L.And a b []

bor :: L.Operand -> L.Operand -> Codegen L.Operand
bor a b = instr_b $ L.Or a b []

cons :: LCONSTANT.Constant -> L.Operand
cons = L.ConstantOperand



---------------------------------------------------------------------------------
------ Basic control flow operations ------
---------------------------------------------------------------------------------

br :: L.Name -> Codegen (L.Named L.Terminator)
br val = terminator $ L.Do $ L.Br val []

cbr :: L.Operand -> L.Name -> L.Name -> Codegen (L.Named L.Terminator)
cbr cond tr fl = terminator $ L.Do $ L.CondBr cond tr fl []

phi :: L.Type -> [(L.Operand, L.Name)] -> Codegen L.Operand
phi typ incoming = instr typ $ L.Phi typ incoming []

ret :: Maybe L.Operand -> Codegen (L.Named L.Terminator)
ret val = terminator $ L.Do $ L.Ret val []


------ "Effect" instructions ------

call :: L.Operand -> [L.Operand] -> L.Type -> Codegen L.Operand
call fn args typ = instr typ $ L.Call Nothing LCALLCONV.C [] (Right fn) (toArgs args) [] []

callVoid :: L.Operand -> [L.Operand] -> Codegen ()
callVoid fn args = unnamedInstr $ L.Call Nothing LCALLCONV.C [] (Right fn) (toArgs args) [] []

alloca :: L.Type -> Codegen L.Operand
alloca ty = instr ty $ L.Alloca ty Nothing 0 []

store :: L.Operand -> L.Operand -> Codegen ()
store ptr@(L.LocalReference typ _) val = unnamedInstr $ L.Store False ptr val Nothing 0 []

load :: L.Operand -> Codegen L.Operand
load ptr@(L.LocalReference typ _) = instr typ $ L.Load False ptr Nothing 0 []

createBlocks :: CodegenState -> [LGLOBAL.BasicBlock]
createBlocks m = map makeBlock $ sortBlocks $ Map.toList (blocks m)

execCodegen :: [(String, L.Operand)] -> Structs -> Map.Map L.Name [ABS.Type] -> Codegen a -> CodegenState
execCodegen vars structs argtyps m = execState (runCodegen m) emptyCodegen { symtab = vars, allStructs = structs, argTypes = argtyps }

entryBlockName :: String
entryBlockName = "entry"

makeBlock :: (L.Name, BlockState) -> L.BasicBlock
makeBlock (label, BlockState _ stack term) = L.BasicBlock label (reverse stack) (maketerm term)
  where
    maketerm (Just x) = x
    maketerm Nothing = error ("Block has no terminator ")

sortBlocks :: [(L.Name, BlockState)] -> [(L.Name, BlockState)]
sortBlocks = sortBy (compare `on` (idx . snd))

emptyCodegen :: CodegenState
emptyCodegen = CodegenState (name' entryBlockName) Map.empty Map.empty [] 1 0 Map.empty Map.empty

structDefine :: String -> [L.Type] -> LLVM ()
structDefine name types = addDefn (L.TypeDefinition (name' name) (Just (L.StructureType False types)))

getsymtab :: Codegen SymbolTable
getsymtab = gets symtab

restoresymtab :: SymbolTable -> Codegen ()
restoresymtab t = modify (\s -> s { symtab = t })

toArgs :: [L.Operand] -> [(L.Operand, [LATTRIBUTE.ParameterAttribute])]
toArgs = map (\x -> (x, []))

uitofp :: L.Operand -> Codegen L.Operand
uitofp operand = instr_d (L.UIToFP operand double [])

sitofp :: L.Operand -> Codegen L.Operand
sitofp operand = instr float $ L.SIToFP operand double []

getElementPtr :: L.Operand -> [L.Operand] -> L.Type -> Codegen L.Operand
getElementPtr addr indicies typ = instr typ (L.GetElementPtr True addr indicies [])

extractStructFieldValue :: L.Type -> L.Operand -> [W.Word32] -> Codegen L.Operand
extractStructFieldValue stype lop indices = instr stype (L.ExtractValue lop indices [])
