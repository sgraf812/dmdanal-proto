module NbE where

import Exp
import Interpreter
import Control.Monad.Trans.State
import Data.Function (fix)

data NbEValue τ = NbEStuck | NbEFun (NbED τ -> NbED τ) | NbECon Tag [NbED τ] | Syn Exp

type NbED τ = τ (NbEValue τ)

type FreshM = State Int
runFreshM :: FreshM a -> a
runFreshM m = evalState m 0

fresh :: FreshM Name
fresh = do
  n <- get
  put (n+1)
  pure ("_" ++ show n)

reflect :: Exp -> NbEValue (ByName FreshM)
reflect e = Syn e

reify :: NbEValue (ByName FreshM) -> FreshM Exp
reify (Syn e) = return e
reify (NbEFun f) = do
  x <- fresh
  let arg = reflect (Var x)
  body <- unByName $ f (ByName (return arg))
  Lam x <$> reify body
reify (NbECon k ds) = do
  xs <- traverse (const fresh) ds
  es <- traverse (\d -> unByName d >>= reify) ds
  return (foldr (\(x,e) -> Let x e) (ConApp k xs) (zip xs es))
reify NbEStuck = undefined

instance Trace (FreshM v) where
  step _ m = m

instance HasBind (NbED (ByName τ)) where
  bind _ rhs body = body (fix rhs)

instance Domain (NbED (ByName FreshM)) where
  stuck = return NbEStuck
  apply df da = df >>= \v -> case v of
    NbEFun f -> f da
    Syn e       -> ByName $ do
      x <- fresh
      a <- unByName da >>= reify
      return (reflect (Let x a (App e x)))
    _     -> stuck
  fun _ f = return (NbEFun f)
  con k ds = return (NbECon k ds)
  select dv alts = dv >>= \v -> case v of
    NbECon k ds | k ∈ dom alts  -> snd (alts ! k) ds
    Syn _                       -> error "implement later --- seems quite involved, but doable"
    _                           -> stuck

nbe :: Exp -> Exp
nbe e = runFreshM (unByName (eval e emp >>= ByName . reify))
