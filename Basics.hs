{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wall #-}

module Basics where

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Text.Printf (printf)

-----------------------------------------------------------------
-- Create a representation for the language of predicate logic --
-----------------------------------------------------------------

-- a term is a variable, a constant, a function or a predicate
data Term = Constant String
          | Variable VSymbol
          | Function FSymbol [Term]
          deriving (Eq, Ord)

-- convenience constructor
pattern Var v = Variable (VSymbol v)

instance Show Term where
    show (Constant c) = c
    show (Variable (VSymbol v)) = v
    --show (Function fsym ts) = show fsym ++ "(" ++ args ++ ")"
    show (Function fsym ts) = printf "%s(%s)" (show fsym) args
        where args = List.intercalate "," $ map show ts

function :: FSymbol -> [Term] -> Maybe Term
function fsym@(FSymbol _ arity) ts
    | arity == length ts = Just (Function fsym ts)
    | otherwise          = Nothing

newtype VSymbol = VSymbol String deriving (Eq, Ord)
data FSymbol = FSymbol String Int deriving (Eq, Ord)
data PSymbol = PSymbol String Int deriving (Eq, Ord)

instance Show VSymbol where
    show (VSymbol name) = name

instance Show FSymbol where
    show (FSymbol name _) = name

instance Show PSymbol where
    show (PSymbol name _) = name

termFreeVariables :: Term -> Set VSymbol
termFreeVariables (Constant _) = Set.empty
termFreeVariables (Variable v) = Set.singleton v
termFreeVariables (Function _ ts) = Set.unions $ map termFreeVariables ts

-- a formula is an atomic formula, a conjunction, a disjunction, 
-- an implication or a (universally or existentially) quantified formula.
data Formula = Atomic      PSymbol [Term]
             | Conjunction Formula Formula
             | Disjunction Formula Formula
             | Implication Formula Formula
             | ForAll      VSymbol Formula
             | ThereExists VSymbol Formula
             deriving (Eq, Ord)

-- a convenience constructor that can also be used for pattern matching
pattern Proposition name = (Atomic (PSymbol name 0) [])

freeVariables :: Formula -> Set VSymbol
freeVariables (Proposition _) = Set.empty
freeVariables (Atomic _ ts) = Set.unions $ map termFreeVariables ts
freeVariables (Conjunction l r) = leftFV `Set.union` rightFV
    where leftFV = freeVariables l
          rightFV = freeVariables r
freeVariables (Disjunction l r) = leftFV `Set.union` rightFV
    where leftFV = freeVariables l
          rightFV = freeVariables r
freeVariables (Implication a c) = anteFV `Set.union` consFV
    where anteFV = freeVariables a
          consFV = freeVariables c
freeVariables (ForAll v f) = Set.delete v (freeVariables f)
freeVariables (ThereExists v f) = Set.delete v (freeVariables f)

bottom :: Formula
bottom = Proposition "⊥"

instance Show Formula where
    show (Proposition name) = name
    --show (Atomic (PSymbol name _) ts) = name ++ "(" ++ args ++ ")"
    show (Atomic (PSymbol name _) ts) = printf "%s(%s)" name args
        where args = List.intercalate ", " $ map show ts
    show (Conjunction l r) = printf "(%s ⋀ %s)" (show l) (show r)
    show (Disjunction l r) = printf "(%s ⋁ %s)" (show l) (show r)
    show (Implication a c)
        | c == bottom = printf "(¬%s)" (show a)
        | otherwise   = printf "(%s → %s)" (show a) (show c)
    show (ForAll x f) = printf "(∀%s : %s)" (show x) (show f)
    show (ThereExists x f) = printf "(∃%s : %s)" (show x) (show f)

--x1, x2, x3 :: Term
--x1 = Var "x1"
--x2 = Var "x2"
--x3 = Var "x3"
--
--c1, c2 :: Term
--c1 = Constant "c1"
--c2 = Constant "c2"
--
--p, q, r :: Formula
--p = Proposition "P"
--q = Proposition "Q"
--r = Proposition "R"
--
--f, g :: FSymbol
--f = FSymbol "f" 1
--g = FSymbol "g" 1
