module CodegenTypes where

import qualified AbsCPP as Abs
import LLVM.AST
import LLVM.AST.Global
import qualified LLVM.AST as AST

import qualified LLVM.AST.Linkage as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Attribute as A
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.FloatingPointPredicate as FP
import Data.ByteString.Short ( ShortByteString, toShort )
import qualified Data.ByteString.Char8 as BS
import Data.Word
import qualified Data.Map as Map

import qualified LLVM.AST.Constant as LCONSTANT
import qualified LLVM.AST.Float as LFLOAT

type FieldMap = Map.Map String Integer
type StructsMap = Map.Map String FieldMap


---------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

constantVal :: LCONSTANT.Constant -> AST.Operand
constantVal = AST.ConstantOperand

double :: AST.Type
double = FloatingPointType AST.DoubleFP

doubleConstantValOne :: AST.Operand
doubleConstantValOne = constantVal $ LCONSTANT.Float (LFLOAT.Double 1)

doubleConstantValZero :: AST.Operand
doubleConstantValZero = constantVal $ LCONSTANT.Float (LFLOAT.Double 0)

constDouble :: Double -> AST.Operand 
constDouble n = constantVal $ LCONSTANT.Float (LFLOAT.Double n)

int :: AST.Type
int = AST.IntegerType 32

intConstantValOne :: AST.Operand
intConstantValOne = constantVal $ LCONSTANT.Int 32 1

intConstantValZero :: AST.Operand
intConstantValZero = constantVal $ LCONSTANT.Int 32 0

intConstantValNegOne :: AST.Operand
intConstantValNegOne = constantVal $ LCONSTANT.Int 32 $ -1

constInt :: Integer -> AST.Operand
constInt n = constantVal $ LCONSTANT.Int 32 n

bool :: AST.Type
bool = AST.IntegerType 1

false :: AST.Operand
false = constantVal $ LCONSTANT.Int 1 0

true :: AST.Operand
true = constantVal $ LCONSTANT.Int 1 1

void :: AST.Type
void = AST.VoidType

castType :: Abs.Type -> AST.Type
castType Abs.Type_bool = bool
castType Abs.Type_int = int
castType Abs.Type_double = double
castType Abs.Type_void = void
castType (Abs.TypeId (Abs.Id id)) = AST.NamedTypeReference $ castName id

castToShortByteString :: String -> ShortByteString
castToShortByteString = toShort . BS.pack

castName :: String -> AST.Name
castName = AST.Name . castToShortByteString


defaultValues :: Abs.Type -> Maybe AST.Operand -- TODO remove the default values, except for voids
defaultValues Abs.Type_bool    = Just false
defaultValues Abs.Type_int     = Just intConstantValZero
defaultValues Abs.Type_double  = Just doubleConstantValZero
defaultValues Abs.Type_void    = Nothing


setStruct :: String -> [Abs.Field] -> StructsMap -> StructsMap
setStruct structName fields = Map.insert structName (castFields fields)

castField :: (Integer, Abs.Field) -> (String, Integer)
castField (index, Abs.FDecl typ (Abs.Id name)) = (name, index)

castFields :: [Abs.Field] -> FieldMap
castFields fields = Map.fromList $ zipWith (curry castField) [0..] fields


getStructField :: String -> String -> StructsMap -> Integer
getStructField struct field structsMap  = helper $ Map.lookup field $ helper $ Map.lookup struct structsMap where
    helper :: Maybe a -> a
    helper (Just a) = a
    helper Nothing = undefined