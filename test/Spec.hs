import Test.QuickCheck
import Test.QuickCheck.Function
import GHC.Generics
import Lib

arbitraryBexp :: Int -> Gen Bexp
arbitraryBexp 0 = elements [TRUE, FALSE]
arbitraryBexp d = elements [Neg (arbitraryBexp (d-1))]

instance Arbitrary Bexp where
  arbitrary = sized arbitraryBexp

prop_b_val :: Fun Var Z -> Bexp -> Bexp -> Bool
prop_b_val s a b = b_val (And a b) (apply s) == b_val (And b a) (apply s)

main :: IO ()
main = quickCheck prop_b_val
