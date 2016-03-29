{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wall #-}

module Deductions where

import Basics
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Printf (printf)

data AssumptionVariable = AVar String Formula deriving (Eq, Ord)
instance Show AssumptionVariable where
    show (AVar name formula) = printf "%s : %s" name (show formula)

data Deduction
    = Assumption            AssumptionVariable
    | ImplicationIntro      Deduction Deduction
    | ImplicationElim       Deduction Deduction
    | ConjunctionIntro      Deduction Deduction
    | ConjunctionElim       Deduction Deduction
    | LeftDisjunctionIntro  Deduction Formula
    | RightDisjunctionIntro Deduction Formula
    | DisjunctionElim       Deduction Deduction Deduction

assumptions :: Deduction -> Set AssumptionVariable
assumptions (Assumption av) = Set.singleton av
assumptions (ImplicationIntro sd1 sd2) = (assumptions sd2) `Set.difference` (assumptions sd1)
assumptions (ImplicationElim sd1 sd2) = (assumptions sd1) `Set.union` (assumptions sd2)
assumptions (ConjunctionIntro sd1 sd2) = (assumptions sd1) `Set.union` (assumptions sd2)
assumptions (ConjunctionElim sd1 sd2) = conjunctionElimAssumptions sd1 sd2
assumptions (LeftDisjunctionIntro sd1 _) = (assumptions sd1)
assumptions (RightDisjunctionIntro sd1 _) = (assumptions sd1)
assumptions (DisjunctionElim sd1 sd2 sd3) = disjunctionElimAssumptions sd1 sd2 sd3

conjunctionElimAssumptions :: Deduction -> Deduction -> Set AssumptionVariable
conjunctionElimAssumptions sd1 sd2 = (assumptions sd1) `Set.union` (Set.filter predicate (assumptions sd2))
        where predicate (AVar _ f) = case (decorate sd1) of
                (Conjunction l r) -> not (f == l || f == r)
                _                 -> error "Must apply conjunction elimination only to a conjunction"

disjunctionElimAssumptions :: Deduction -> Deduction -> Deduction -> Set AssumptionVariable
disjunctionElimAssumptions sd1 sd2 sd3 = Set.unions [av1, av2, av3]
    where av1 = assumptions sd1
          av2 = Set.filter predicate $ assumptions sd2
          av3 = Set.filter predicate $ assumptions sd3
          predicate (AVar _ f) = case (decorate sd1) of
              (Disjunction l r) -> not (f == l || f == r)
              _                 -> error "Must apply disjunction elimination only to a disjunction"

decorate :: Deduction -> Formula
decorate (Assumption (AVar _ f)) = f
decorate (ImplicationIntro a c) = (decorate a) #> (decorate c)
decorate (ImplicationElim sd1 ded) = case (decorate sd1) of
    (Implication a c) ->
        if a == decorate ded
            then c
            else error "Must apply implication elimination only to implications" 
    _ -> error "Must apply implication elimination only to implications"
decorate (ConjunctionIntro l r) = (decorate l) #& (decorate r)
decorate (ConjunctionElim _ d) = decorate d
decorate (LeftDisjunctionIntro d rf) = (decorate d) #| rf
decorate (RightDisjunctionIntro d lf) = lf #| (decorate d)
decorate (DisjunctionElim _ sd2 _) = decorate sd2

instance Show Deduction where
    show d = printf "{%s} ⊢ %s" assump decor
        where assump = List.intercalate ", " $ map show $ Set.toList $ assumptions d
              decor = show (decorate d)

p, q, pq :: Formula
p = Proposition "P"
q = Proposition "Q"
pq = p #> q

uP, uQ, uPQ :: AssumptionVariable
uP = AVar "u" p
uQ = AVar "v" q
uPQ = AVar "w" pq

u, v, w :: Deduction
u = Assumption uP
v = Assumption uQ
w = Assumption uPQ

ie :: Deduction
ie = ImplicationElim w u
