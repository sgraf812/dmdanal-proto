import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit
import Exp
import Interpreter
import DmdAnal

import Data.List
import Data.Ord
import System.Timeout
import Control.Monad.IO.Class (liftIO)
import GHC.Exts

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

golden :: String -> String -> SubDemand -> String -> TestTree
golden info input sd output = testCase info $ do
  let expected = output
  mb_actual <- liftIO $ timeout 100000 (return $! lazy (show (dmdAnal (read input) sd)))
  case mb_actual of
    Nothing     -> assertFailure "diverges"
    Just actual -> actual == expected @? "expected: " ++ expected ++ "\n but got: " ++ actual

unitTests = testGroup "Unit tests"
  [ golden "const expr"
           "λx.λy.x"
           (callCtx 2)
           "{}|>λ1*U.{}|>λA.{}|>."
  , golden "const binding"
           "let const = λx.λy.x in const"
           (callCtx 2)
           "{}|>λ1*U.{}|>λA.{}|>."
  , golden "eta-expandable loop with call in exit"
           "let loop = λx.case x of {\
           \   TT() -> loop z;\
           \   FF() -> f } in \
           \case b of { \
           \   TT() -> loop y;\
           \   FF() -> λz. z }"
           (callCtx 2)
           "{b↦1*HU,f↦1*Ap[1;Ap[1;U]],y↦1*HU,z↦ω*HU}|>."
  , golden "DataCon values Some(const)"
           "let const = λx.λy.x in \
           \let z = Some(const) in \
           \case z of { Some(f) -> f x1 x2; None() -> x3 }"
           Top
           "{x1↦1*U}|>."
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

