---------------------------------------------------------------
-- Language Engineering: COMS22201
-- Assessed Coursework 2: CWK2
-- Question 1: Denotational Semantics of While with read/write
---------------------------------------------------------------
-- This stub file provides a set of Haskell type definitions
-- you should use to implement various functions and examples
-- associated with the denotational semantics of While with
-- read and write statements as previously used in CWK1.
--
-- To answer this question, upload one file "cwk2.hs" to the
-- "CWK2" unit component in SAFE by midnight on 01/05/2016.
--
-- You should ensure your file loads in GHCI with no errors
-- and it does not import any modules (other than Prelude).
--
-- Please note that you will loose marks if your submission
-- is late, incorrectly named, generates load errors,
-- or if you modify any of the type definitions below.
--
-- For further information see the brief at the following URL:
-- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/cwk2.pdf
---------------------------------------------------------------
module Cwk2 where

import Prelude hiding (Num)
import qualified Prelude (Num)

type Num = Integer
type Var = String
type Z = Integer
type T = Bool
type State = Var -> Z
type Input  = [Integer]  -- to denote the values read by a program
type Output = [String]   -- to denote the strings written by a program
type IOState = (Input,Output,State)  -- to denote the combined inputs, outputs and state of a program

data Aexp = N Num | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp deriving (Show, Eq, Read)
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm
          | Read Var       -- for reading in the value of a variable
          | WriteA Aexp    -- for writing out the value of an arithmetic expression
          | WriteB Bexp    -- for writing out the value of a Boolean expression
          | WriteS String  -- for writing out a given string
          | WriteLn        -- for writing out a string consisting of a newline character
          deriving (Show, Eq, Read)

---------------------------------------------------------------
-- Part A)
--
-- Begin by adding your definitions of the following functions
-- that you previously wrote as part of CWK2p1 and CWk2p2:
---------------------------------------------------------------

-- Based on nub, http://hackage.haskell.org/package/base-4.8.2.0/docs/src/Data.OldList.html#nub
-- Warning: n^2 complexity!
removeDuplicates :: (Eq a) => [a] -> [a]
removeDuplicates [] =  []
removeDuplicates (x:xs) = x : removeDuplicates (filter (\ y -> x /= y) xs)

fv_aexp :: Aexp -> [Var]
fv_aexp (N n) = []
fv_aexp (V v) = [v]
fv_aexp (Add a b) = removeDuplicates $ (fv_aexp a) ++ (fv_aexp b)
fv_aexp (Mult a b) = removeDuplicates $ (fv_aexp a) ++ (fv_aexp b)
fv_aexp (Sub a b) = removeDuplicates $ (fv_aexp a) ++ (fv_aexp b)

fv_bexp :: Bexp -> [Var]
fv_bexp TRUE = []
fv_bexp FALSE = []
fv_bexp (Eq a1 a2) = removeDuplicates $ (fv_aexp a1) ++ (fv_aexp a2)
fv_bexp (Le a1 a2) = removeDuplicates $ (fv_aexp a1) ++ (fv_aexp a2)
fv_bexp (Neg b) = fv_bexp b
fv_bexp (And b1 b2) = removeDuplicates $ (fv_bexp b1) ++ (fv_bexp b2)

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

cond :: (a->T, a->a, a->a) -> (a->a)
cond (b, p, q) s = if b s then p s else q s

cond' :: (c->T, (a,b,c)->(a,b,c), (a,b,c)->(a,b,c)) -> ((a,b,c)->(a,b,c))
cond' (b, p, q) (i,o,s) = if b s then p (i,o,s) else q (i,o,s)

fix :: (a -> a) -> a
fix f = let x = f x in x

update :: State -> Z -> Var -> State
update s i v var = if var == v then i else s var

---------------------------------------------------------------
-- Part B))
--
-- Write a function fv_stm with the following signature such that
-- fv_stm p returns the set of (free) variables appearing in p:
---------------------------------------------------------------

fv_stm :: Stm -> [Var]
fv_stm (Ass v a) = v : fv_aexp a
fv_stm Skip = []
fv_stm (Comp s1 s2) = removeDuplicates $ (fv_stm s1) ++ (fv_stm s2)
fv_stm (If b s1 s2) = removeDuplicates $ (fv_bexp b) ++ (fv_stm s1) ++ (fv_stm s2)
fv_stm (While b s) = removeDuplicates $ (fv_bexp b) ++ (fv_stm s)
fv_stm (Read v) = [v]
fv_stm (WriteA a) = fv_aexp a
fv_stm (WriteB b) = fv_bexp b
fv_stm (WriteS s)  = []
fv_stm (WriteLn) = []

---------------------------------------------------------------
-- Part C)
--
-- Define a constant fac representing the following program
-- (which you may recall from the file test7.w used in CWK1):
{--------------------------------------------------------------
write('Factorial calculator'); writeln;
write('Enter number: ');
read(x);
write('Factorial of '); write(x); write(' is ');
y := 1;
while !(x=1) do (
  y := y * x;
  x := x - 1
);
write(y);
writeln;
writeln
---------------------------------------------------------------}

fac :: Stm
fac = Comp
        (WriteS "Factorial calculator")
        (Comp
          WriteLn
          (Comp
            (WriteS "Enter number: ")
            (Comp
              (Read "x")
              (Comp
                (WriteS "Factorial of ")
                (Comp
                  (WriteA (V "x"))
                  (Comp
                    (WriteS " is ")
                    (Comp
                      (Ass "y" (N 1))
                      (Comp
                        (While
                          (Neg (Eq (V "x") (N 1)))
                          (Comp
                            (Ass "y" (Mult (V "y") (V "x")))
                            (Ass "y" (Sub (V "x") (N 1)))))
                        (Comp
                          (WriteA (V "y"))
                          (Comp WriteLn WriteLn))))))))))

---------------------------------------------------------------
-- Part D)
--
-- Define a constant pow representing the following program
-- (which you may recall from the file test7.w used in CWK1):
{--------------------------------------------------------------
write('Exponential calculator'); writeln;
write('Enter base: ');
read(base);
if 1 <= base then (
  write('Enter exponent: ');
  read(exponent);
  num := 1;
  count := exponent;
  while 1 <= count do (
    num := num * base;
    count := count - 1
  );
  write(base); write(' raised to the power of '); write(exponent); write(' is ');
  write(num)
) else (
  write('Invalid base '); write(base)
);
writeln
---------------------------------------------------------------}

pow :: Stm
pow = Comp
        (WriteS "Exponential calculator")
        (Comp
          WriteLn
          (Comp
            (WriteS "Enter base: ")
            (Comp
              (Read "base")
              (Comp
                (If
                  (Le (N 1) (V "base"))
                  (Comp
                    (WriteS "Enter exponent: ")
                    (Comp
                      (Read "exponent")
                      (Comp
                        (Ass "num" (N 1))
                        (Comp
                          (Ass "count" (V "exponent"))
                          (Comp
                            (While
                              (Le (N 1) (V "count"))
                              (Comp
                                (Ass "num" (Mult (V "num") (V "base")))
                                (Ass "count" (Sub (V "count") (N 1)))))
                            (Comp
                              (WriteA (V "base"))
                              (Comp
                                (WriteS " raised to the power of ")
                                (Comp
                                  (WriteA (V "exponent"))
                                  (Comp
                                    (WriteS " is ")
                                    (WriteA (V "num")))))))))))
                  (Comp (WriteS "Invalid base ") (WriteA (V "base"))))
                WriteLn))))

---------------------------------------------------------------
-- Part E)
--
-- Write a function s_ds with the following signature such that
-- s_ds p (i,o,s) returns the result of semantically evaluating
-- program p in state s with input list i and output list o.
---------------------------------------------------------------

s_ds :: Stm -> IOState -> IOState
s_ds (Ass v a) (i,o,s) = (i, o, update s (a_val a s) v)
s_ds Skip ss = ss
s_ds (Comp s1 s2) ss = (s_ds s2 . s_ds s1) ss
s_ds (If c t e) (i,o,s) = cond' (b_val c, s_ds t, s_ds e) (i,o,s)
s_ds (While c stm) s = fix (\g -> cond' (b_val c, g . s_ds stm, id)) s
s_ds (Read v) (i:is,o,s) = (is, o, update s i v)
s_ds (WriteA a) (i,o,s) = (i, o ++ [show $ a_val a s], s)
s_ds (WriteB b) (i,o,s) = (i, o ++ [show $ b_val b s], s)
s_ds (WriteS str) (i,o,s) = (i, o ++ [str], s)
s_ds WriteLn (i,o,s) = (i, o ++ ["\n"], s)

---------------------------------------------------------------
-- Part F)
--
-- Write a function eval with the following signature such that
-- eval p (i,o,s) computes the result of semantically evaluating
-- program p in state s with input list i and output list o; and
-- then returns the final input list and output list together
-- with a list of the variables appearing in the program and
-- their respective values in the final state.
---------------------------------------------------------------

eval :: Stm -> IOState -> (Input, Output, [Var], [Num])
eval = undefined
