---------------------------------------------------------------
-- Language Engineering: COMS22201
-- CWK2p2: Denotational Semantics of statements
-- Due: Sunday 20th March (for formative feedback only)
---------------------------------------------------------------
-- This stub file provides a set of Haskell type definitions
-- you should use to implement some functions and examples
-- associated with the denotational semantics of program
-- statements in the While programming language as described
-- in the course text book by Nielson and Nielson.
--
-- These functions are defined in the lecture notes and
-- in Chapter 4 of the book. Hints on their implementation
-- can be found in the lab exercises and the Miranda code
-- in Appendix D of the book.
--
-- You should submit one file "cwk2p2.hs" into the "CWK2p2"
-- unit component in SAFE by midnight on Sunday 20th March.
--
-- You should ensure your file loads in GHCI with no errors
-- and it does not import any modules (other than Prelude).
--
-- Please note that your submission will NOT be marked if
-- it is late, incorrectly named, generates load errors,
-- or if you modify any of the type definitions below.
---------------------------------------------------------------
module Cwk2P2 where

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
-- QUESTION 0)
-- First include your definitions of a_val and b_val from CWK2p1
---------------------------------------------------------------

a_val :: Aexp -> State -> Z
a_val (N n) _ = n
a_val (V v) s = s v
a_val (Add l r) s = a_val l s + a_val r s
a_val (Mult l r) s = a_val l s * a_val r s
a_val (Sub l r) s = a_val l s - a_val r s

b_val :: Bexp -> State -> T
b_val TRUE _ = True
b_val FALSE _ = False
b_val (Eq l r) s = a_val l s == a_val r s
b_val (Le l r) s = a_val l s <= a_val r s
b_val (Neg b) s = not (b_val b s)
b_val (And l r) s = b_val l s && b_val r s

---------------------------------------------------------------
-- QUESTION 1)
-- Write a function cond with the following signature such that
-- cond (b,p,q) s returns p s if b s is true and q s otherwise
---------------------------------------------------------------

cond :: (a -> T, a -> a, a -> a) -> (a -> a)
cond (b, p, q) s = if b s then p s else q s

---------------------------------------------------------------
-- QUESTION 2)
-- Write a function fix with the following signature such that
-- fix f simply returns f (fix f)
---------------------------------------------------------------

fix :: (a -> a) -> a
fix f = let x = f x in x

---------------------------------------------------------------
-- QUESTION 3)
-- Write a function update with the following signature such that
-- update s i v returns the state update s[v |-> i]
-- i.e. state obtained from s by updating the value of v to i
---------------------------------------------------------------

update :: State -> Z -> Var -> State
update s i v var = if var == v then i else s var

---------------------------------------------------------------
-- QUESTION 4)
-- Write a function s_ds with the following signature such that
-- s_ds p s returns the result of semantically evaluating program p in state s:
---------------------------------------------------------------

s_ds :: Stm -> State -> State
s_ds (Ass v a) s = update s (a_val a s) v
s_ds Skip s = s
s_ds (Comp s1 s2) s = (s_ds s2 . s_ds s1) s
s_ds (If c t e) s = cond (b_val c, s_ds t, s_ds e) s
s_ds (While c stm) s = fix (\g -> cond (b_val c, g . s_ds stm, id)) s

---------------------------------------------------------------
-- QUESTION 5)
-- Define a constant p that represents the following program
-- y:=1 ; while ¬(x=1) do (y:=y*x; x:=x-1)
---------------------------------------------------------------

p :: Stm
p = Comp
      (Ass "y" (N 1))
      (While
        (Neg (Eq (V "x") (N 1)))
        (Comp
          (Ass "y" (Mult (V "y") (V "x")))
          (Ass "x" (Sub (V "x") (N 1)))))

--(Ass "y" (Mult (V "y") (V "x")))

p2 :: Stm
p2 = While
        (Neg (Eq (V "x") (N 2)))
        (Ass "x" (N 2))

---------------------------------------------------------------
-- QUESTION 6)
-- Define a constant s that represents the state that maps
-- x to 5, y to 2, and every other variable to 0
---------------------------------------------------------------

s :: State
s "x" = 5
s "y" = 2
s _ = 0

---------------------------------------------------------------
-- QUESTION 7)
-- Verify using your denotational semantics that p computes 5!
-- when it is applied to the state s
---------------------------------------------------------------

s_after :: State
s_after = s_ds p s
