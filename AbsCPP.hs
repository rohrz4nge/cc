-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The abstract syntax of language CPP.

module AbsCPP where

import Prelude (Double, Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

data Program = PDefs [Def]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Def = DFun Type Id [Arg] [Stm] | DStruct Id [Field]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Field = FDecl Type Id
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Arg = ADecl Type Id
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Stm
    = SExp Exp
    | SDecls Type [IdIn]
    | SReturn Exp
    | SReturnV
    | SWhile Exp Stm
    | SDoWhile Stm Exp
    | SFor Exp Exp Exp Stm
    | SBlock [Stm]
    | SIfElse Exp Stm Stm
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data IdIn = IdNoInit Id | IdInit Id Exp
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Exp
    = ETrue
    | EFalse
    | EInt Integer
    | EDouble Double
    | EId Id
    | EApp Id [Exp]
    | EProj Exp Id
    | EPIncr Exp
    | EPDecr Exp
    | EIncr Exp
    | EDecr Exp
    | EUPlus Exp
    | EUMinus Exp
    | ETimes Exp Exp
    | EDiv Exp Exp
    | EPlus Exp Exp
    | EMinus Exp Exp
    | ETwc Exp Exp
    | ELt Exp Exp
    | EGt Exp Exp
    | ELtEq Exp Exp
    | EGtEq Exp Exp
    | EEq Exp Exp
    | ENEq Exp Exp
    | EAnd Exp Exp
    | EOr Exp Exp
    | EAss Exp Exp
    | ECond Exp Exp Exp
    | ETyped Exp Type
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Type
    = Type_bool | Type_int | Type_double | Type_void | TypeId Id
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype Id = Id String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

