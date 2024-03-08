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

tests :: TestTree
tests = testGroup "Tests" [unitTests]

golden :: String -> String -> SubDemand -> String -> TestTree
golden info input sd output = testCase info $ do
  let expected = output
  let actual   = show (dmdAnal (read input) sd)
  actual == expected @? "expected: " ++ expected ++ "\n but got: " ++ actual

unitTests = testGroup "Unit tests"
  [ golden "const expr"
           "λx.λy.x"
           (callCtx 2)
           "{}|>λ1*U.{}|>λA.{}|>."
  , golden "const binding"
           "let const = λx.λy.x in const"
           (callCtx 2)
           "{}|>λ1*U.{}|>λA.{}|>."
  , golden "recursive tail call of free var"
           "let recfun = λx.case x of {\
           \   TT() -> recfun z;\
           \   FF() -> f } in \
           \case b of { \
           \   TT() -> recfun y;\
           \   FF() -> λz. z }"
           (callCtx 2)
           "{b↦1*HU,f↦1*Ap[1;Ap[1;U]],y↦1*HU,z↦ω*HU}|>."
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

