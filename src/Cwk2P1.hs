---------------------------------------------------------------
-- Language Engineering: COMS22201
-- CWK2p1: Denotational Semantics of Arithmetics and Booleans
-- Due: Sunday 6th March (for formative feedback only)
---------------------------------------------------------------
-- This stub file provides a set of Haskell type definitions
-- that you should use to implement six functions associated
-- with the denotational semantics of arithmetic and Boolean
-- expressions in the While programming language as described
-- in the course text book by Nielson and Nielson.
--
-- These six functions are defined in the lecture notes and
-- in Chapter 1 of the book. Hints on their implementation
-- can be found in the lab exercises and the Miranda code
-- in Appendix B of the book.
--
-- You should submit one file "cwk2p1.hs" into the "CWK2p1"
-- unit component in SAFE by midnight on Sunday 6th March.
--
-- You should ensure your file loads in GHCI with no errors
-- and it does not import any modules (other than Prelude).
--
-- Please note that your submission will NOT be marked if
-- it is late, incorrectly named, generates load errors,
-- or if you modify any of the type definitions below.
---------------------------------------------------------------
module Cwk2P1 where

import Prelude hiding (Num)
import qualified Prelude (Num)

type Num = Integer
type Var = String
type Z = Integer
type T = Bool
type State = Var -> Z

data Aexp = N Num | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp deriving (Show, Eq, Read)
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm deriving (Show, Eq, Read)

---------------------------------------------------------------
-- QUESTION 1)
-- Write a function fv_aexp with the following signature such that
-- fv_aexp a returns the set of (free) variables in a:
---------------------------------------------------------------

fv_aexp :: Aexp -> [Var]
fv_aexp (N n) = []
fv_aexp (V v) = [v]
fv_aexp (Add a b) = (fv_aexp a) ++ (fv_aexp b)
fv_aexp (Mult a b) = (fv_aexp a) ++ (fv_aexp b)
fv_aexp (Sub a b) = (fv_aexp a) ++ (fv_aexp b)

---------------------------------------------------------------
-- QUESTION 2)
-- Write a function fv_bexp with the following signature such that
-- fv_bexp b returns the set of (free) variables in b:
---------------------------------------------------------------

fv_bexp :: Bexp -> [Var]
fv_bexp TRUE = []
fv_bexp FALSE = []
fv_bexp (Eq a1 a2) = (fv_aexp a1) ++ (fv_aexp a2)
fv_bexp (Le a1 a2) = (fv_aexp a1) ++ (fv_aexp a2)
fv_bexp (Neg b) = fv_bexp b
fv_bexp (And b1 b2) = (fv_bexp b1) ++ (fv_bexp b2)

---------------------------------------------------------------
-- QUESTION 3)
-- Write a function subst_aexp with the following signature such that
-- subst_aexp a1 v a2 returns the result of replacing all occurences of v in a1 by a2:
---------------------------------------------------------------

subst_aexp :: Aexp -> Var -> Aexp -> Aexp
subst_aexp (N n) _ _ = N n
subst_aexp (V a1) v a2 = if a1 == v then a2 else V a1
subst_aexp (Add l r) v a2 = Add (subst_aexp l v a2) (subst_aexp r v a2)
subst_aexp (Mult l r) v a2 = Mult (subst_aexp l v a2) (subst_aexp r v a2)
subst_aexp (Sub l r) v a2 = Sub (subst_aexp l v a2) (subst_aexp r v a2)

---------------------------------------------------------------
-- QUESTION 4)
-- Write a function subst_bexp with the following signature such that
-- subst_bexp b v a returns the result of replacing all occurences of v in b by a:
---------------------------------------------------------------

subst_bexp :: Bexp -> Var -> Aexp -> Bexp
subst_bexp TRUE _ _ = TRUE
subst_bexp FALSE _ _ = FALSE
subst_bexp (Eq l r) v a = Eq (subst_aexp l v a) (subst_aexp r v a)
subst_bexp (Le l r) v a = Le (subst_aexp l v a) (subst_aexp r v a)
subst_bexp (Neg b) v a = Neg (subst_bexp b v a)
subst_bexp (And l r) v a = And (subst_bexp l v a) (subst_bexp r v a)

---------------------------------------------------------------
-- QUESTION 5)
-- Write a function a_val with the following signature such that
-- a_val a s returns the result of semantically evaluating expression a in state s:
---------------------------------------------------------------

a_val :: Aexp -> State -> Z
a_val (N n) _ = n
a_val (V v) s = s v
a_val (Add l r) s = (a_val l s) + (a_val r s)
a_val (Mult l r) s = (a_val l s) * (a_val r s)
a_val (Sub l r) s = (a_val l s) - (a_val r s)

---------------------------------------------------------------
-- QUESTION 6)
-- Write a function b_val with the following signature such that
-- b_val b s returns the result of semantically evaluating expression b in state s:
---------------------------------------------------------------

b_val :: Bexp -> State -> T
b_val TRUE _ = True
b_val FALSE _ = False
b_val (Eq l r) s = (a_val l s) == (a_val r s)
b_val (Le l r) s = (a_val l s) <= (a_val r s)
b_val (Neg b) s = not (b_val b s)
b_val (And l r) s = (b_val l s) && (b_val r s)
