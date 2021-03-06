{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for PrintCPP.
--   Generated by the BNF converter.

module PrintCPP where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, dropWhile, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsCPP

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i = \case
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    [";"]        -> showChar ';'
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i     = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt     _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print AbsCPP.Id where
  prt _ (AbsCPP.Id i) = doc $ showString i
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print AbsCPP.Program where
  prt i = \case
    AbsCPP.PDefs defs -> prPrec i 0 (concatD [prt 0 defs])

instance Print AbsCPP.Def where
  prt i = \case
    AbsCPP.DFun type_ id_ args stms -> prPrec i 0 (concatD [prt 0 type_, prt 0 id_, doc (showString "("), prt 0 args, doc (showString ")"), doc (showString "{"), prt 0 stms, doc (showString "}")])
    AbsCPP.DStruct id_ fields -> prPrec i 0 (concatD [doc (showString "struct"), prt 0 id_, doc (showString "{"), prt 0 fields, doc (showString "}"), doc (showString ";")])
  prtList _ [] = concatD []
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [AbsCPP.Def] where
  prt = prtList

instance Print AbsCPP.Field where
  prt i = \case
    AbsCPP.FDecl type_ id_ -> prPrec i 0 (concatD [prt 0 type_, prt 0 id_])
  prtList _ [x] = concatD [prt 0 x, doc (showString ";")]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [AbsCPP.Field] where
  prt = prtList

instance Print AbsCPP.Arg where
  prt i = \case
    AbsCPP.ADecl type_ id_ -> prPrec i 0 (concatD [prt 0 type_, prt 0 id_])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsCPP.Arg] where
  prt = prtList

instance Print AbsCPP.Stm where
  prt i = \case
    AbsCPP.SExp exp -> prPrec i 0 (concatD [prt 0 exp, doc (showString ";")])
    AbsCPP.SDecls type_ idins -> prPrec i 0 (concatD [prt 0 type_, prt 0 idins, doc (showString ";")])
    AbsCPP.SReturn exp -> prPrec i 0 (concatD [doc (showString "return"), prt 0 exp, doc (showString ";")])
    AbsCPP.SReturnV -> prPrec i 0 (concatD [doc (showString "return"), doc (showString ";")])
    AbsCPP.SWhile exp stm -> prPrec i 0 (concatD [doc (showString "while"), doc (showString "("), prt 0 exp, doc (showString ")"), prt 0 stm])
    AbsCPP.SDoWhile stm exp -> prPrec i 0 (concatD [doc (showString "do"), prt 0 stm, doc (showString "while"), doc (showString "("), prt 0 exp, doc (showString ")"), doc (showString ";")])
    AbsCPP.SFor exp1 exp2 exp3 stm -> prPrec i 0 (concatD [doc (showString "for"), doc (showString "("), prt 0 exp1, doc (showString ";"), prt 0 exp2, doc (showString ";"), prt 0 exp3, doc (showString ")"), prt 0 stm])
    AbsCPP.SBlock stms -> prPrec i 0 (concatD [doc (showString "{"), prt 0 stms, doc (showString "}")])
    AbsCPP.SIfElse exp stm1 stm2 -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 exp, doc (showString ")"), prt 0 stm1, doc (showString "else"), prt 0 stm2])
  prtList _ [] = concatD []
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [AbsCPP.Stm] where
  prt = prtList

instance Print AbsCPP.IdIn where
  prt i = \case
    AbsCPP.IdNoInit id_ -> prPrec i 0 (concatD [prt 0 id_])
    AbsCPP.IdInit id_ exp -> prPrec i 0 (concatD [prt 0 id_, doc (showString "="), prt 0 exp])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsCPP.IdIn] where
  prt = prtList

instance Print AbsCPP.Exp where
  prt i = \case
    AbsCPP.ETrue -> prPrec i 15 (concatD [doc (showString "true")])
    AbsCPP.EFalse -> prPrec i 15 (concatD [doc (showString "false")])
    AbsCPP.EInt n -> prPrec i 15 (concatD [prt 0 n])
    AbsCPP.EDouble d -> prPrec i 15 (concatD [prt 0 d])
    AbsCPP.EId id_ -> prPrec i 15 (concatD [prt 0 id_])
    AbsCPP.EApp id_ exps -> prPrec i 14 (concatD [prt 0 id_, doc (showString "("), prt 0 exps, doc (showString ")")])
    AbsCPP.EProj exp id_ -> prPrec i 14 (concatD [prt 14 exp, doc (showString "."), prt 0 id_])
    AbsCPP.EPIncr exp -> prPrec i 14 (concatD [prt 14 exp, doc (showString "++")])
    AbsCPP.EPDecr exp -> prPrec i 14 (concatD [prt 14 exp, doc (showString "--")])
    AbsCPP.EIncr exp -> prPrec i 13 (concatD [doc (showString "++"), prt 13 exp])
    AbsCPP.EDecr exp -> prPrec i 13 (concatD [doc (showString "--"), prt 13 exp])
    AbsCPP.EUPlus exp -> prPrec i 13 (concatD [doc (showString "+"), prt 13 exp])
    AbsCPP.EUMinus exp -> prPrec i 13 (concatD [doc (showString "-"), prt 13 exp])
    AbsCPP.ETimes exp1 exp2 -> prPrec i 12 (concatD [prt 12 exp1, doc (showString "*"), prt 13 exp2])
    AbsCPP.EDiv exp1 exp2 -> prPrec i 12 (concatD [prt 12 exp1, doc (showString "/"), prt 13 exp2])
    AbsCPP.EPlus exp1 exp2 -> prPrec i 11 (concatD [prt 11 exp1, doc (showString "+"), prt 12 exp2])
    AbsCPP.EMinus exp1 exp2 -> prPrec i 11 (concatD [prt 11 exp1, doc (showString "-"), prt 12 exp2])
    AbsCPP.ETwc exp1 exp2 -> prPrec i 10 (concatD [prt 10 exp1, doc (showString "<=>"), prt 11 exp2])
    AbsCPP.ELt exp1 exp2 -> prPrec i 9 (concatD [prt 9 exp1, doc (showString "<"), prt 10 exp2])
    AbsCPP.EGt exp1 exp2 -> prPrec i 9 (concatD [prt 9 exp1, doc (showString ">"), prt 10 exp2])
    AbsCPP.ELtEq exp1 exp2 -> prPrec i 9 (concatD [prt 9 exp1, doc (showString "<="), prt 10 exp2])
    AbsCPP.EGtEq exp1 exp2 -> prPrec i 9 (concatD [prt 9 exp1, doc (showString ">="), prt 10 exp2])
    AbsCPP.EEq exp1 exp2 -> prPrec i 8 (concatD [prt 8 exp1, doc (showString "=="), prt 9 exp2])
    AbsCPP.ENEq exp1 exp2 -> prPrec i 8 (concatD [prt 8 exp1, doc (showString "!="), prt 9 exp2])
    AbsCPP.EAnd exp1 exp2 -> prPrec i 4 (concatD [prt 4 exp1, doc (showString "&&"), prt 5 exp2])
    AbsCPP.EOr exp1 exp2 -> prPrec i 3 (concatD [prt 3 exp1, doc (showString "||"), prt 4 exp2])
    AbsCPP.EAss exp1 exp2 -> prPrec i 2 (concatD [prt 3 exp1, doc (showString "="), prt 2 exp2])
    AbsCPP.ECond exp1 exp2 exp3 -> prPrec i 2 (concatD [prt 3 exp1, doc (showString "?"), prt 0 exp2, doc (showString ":"), prt 2 exp3])
    AbsCPP.ETyped exp type_ -> prPrec i 15 (concatD [doc (showString "("), prt 0 exp, doc (showString ":"), prt 0 type_, doc (showString ")")])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsCPP.Exp] where
  prt = prtList

instance Print AbsCPP.Type where
  prt i = \case
    AbsCPP.Type_bool -> prPrec i 0 (concatD [doc (showString "bool")])
    AbsCPP.Type_int -> prPrec i 0 (concatD [doc (showString "int")])
    AbsCPP.Type_double -> prPrec i 0 (concatD [doc (showString "double")])
    AbsCPP.Type_void -> prPrec i 0 (concatD [doc (showString "void")])
    AbsCPP.TypeId id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print [AbsCPP.Id] where
  prt = prtList

