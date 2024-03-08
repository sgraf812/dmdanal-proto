import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit
import Exp
import Interpreter
import DmdAnal

import Data.List
import Data.Ord

main = defaultMain tests

dmdAnal :: String -> DmdD
dmdAnal e = eval (read e) emp

tests :: TestTree
tests = testGroup "Tests" [unitTests]

golden :: String -> String -> SubDemand -> String -> TestTree
golden info input sd output = testCase info $ do
  show (dmdAnal input sd) @?= output

unitTests = testGroup "Unit tests"
  [ golden "const expr" "λx.λy.x"
           (callCtx 2)
           "{}|>λ1*U.{}|>λA.{}|>."
  , golden "const expr" "let const = λx.λy.x in const"
           (callCtx 2)
           "{}|>λ1*U.{}|>λA.{}|>."
  ]

-- qcProps = testGroup "(checked by QuickCheck)"
--   [ QC.testProperty "sort == sort . reverse" $
--       \list -> sort (list :: [Int]) == sort (reverse list)
--   , QC.testProperty "Fermat's little theorem" $
--       \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , QC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 QC.==> x^n + y^n /= (z^n :: Integer)
--   ]

