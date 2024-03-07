{-# LANGUAGE DerivingVia #-}
module DmdAnal where

import Prelude hiding ((+), (*))
import qualified Prelude
import Exp
import Order
import Interpreter
import Data.Functor.Identity
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
-- import Debug.Trace

data U = U0 | U1 | Uω deriving (Eq, Ord)
instance Show U where
  show U0 = "0"
  show U1 = "1"
  show Uω = "ω"
instance Lat U where
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
class UVec a where
  (+)  :: a -> a -> a
  (*)  :: U -> a -> a
infixl 6 +
infixl 7 *
instance UVec U where
  U1 + U1 = Uω
  u1 + u2 = u1 ⊔ u2
  U0 * _ = U0
  _ * U0 = U0
  U1 * u = u
  Uω * _ = Uω
instance (Ord k, UVec u) => UVec (k :-> u) where
  (+) = Map.unionWith (+)
  u * m = Map.map (u *) m

type UNonAbs  = U -- Not U0
type UNonOnce = U -- Not U1

data Demand = Abs | UNonAbs :* SubDemand deriving Eq
data SubDemand
  = Seq                     -- Stop context
  | Top                     -- Uknown context
  | Ap UNonAbs SubDemand    -- Apply context
  | Sel (Tag :-> [Demand])  -- Select context

mkCall :: U -> SubDemand -> SubDemand
mkCall U0 _   = Seq
mkCall Uω Top = Top
mkCall n  sd  = Ap n sd

mkSingleScrut :: Tag -> [Demand] -> SubDemand
mkSingleScrut k ds
  | all (== absDmd) ds = Seq
  | otherwise          = Sel (Map.singleton k ds)

absDmd :: Demand
absDmd = Abs
topDmd :: Demand
topDmd = Uω :* Top

zipWithEqual :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWithEqual f as bs | length as == length bs = zipWith f as bs
                     | otherwise              = error "not same length"

instance Lat Demand where
  bottom = Abs
  Abs ⊔ d = d
  d ⊔ Abs = d
  (u1:*sd1) ⊔ (u2:*sd2) = (u1⊔u2) :* (sd1⊔sd2)
instance Eq SubDemand where
  Seq == Seq = True
  Top == Top = True
  Ap n1 sd1 == Ap n2 sd2 = n1 == n2 && sd1 == sd2
  Sel dmds1 == Sel dmds2 = dmds1 == dmds2 -- NB: assumes that dmds1 and dmds2 are normalised, that is, no all bot entries
  Top == Ap n sd = n == Uω && sd == Top
--  Seq == Sel dmds = all (all (== absDmd)) dmds -- not needed when normalised
--  Sel dmds == Seq = all (all (== absDmd)) dmds -- not needed when normalised
--  Top == Sel dmds = all (all (== topDmd)) dmds -- not true, unless dmds lists all constructors
  _   == _         = False
instance Lat SubDemand where
  bottom = Seq
  Top ⊔ _ = Top
  _ ⊔ Top = Top
  Seq ⊔ sd = sd
  sd ⊔ Seq = sd
  Ap n1 sd1 ⊔ Ap n2 sd2 = mkCall (n1⊔n2) (sd1⊔sd2)
  Sel dmds1 ⊔ Sel dmds2
    = Sel (Map.unionWith (zipWithEqual (⊔)) dmds1 dmds2)
  _ ⊔ _ = Top

instance UVec Demand where
  Abs + d = d
  d + Abs = d
  (_u1:*sd1) + (_u2:*sd2) = Uω :* (sd1+sd2)
  _ * _ = error "unused"

instance UVec SubDemand where
  Top + _ = Top
  _ + Top = Top
  Seq + sd = sd
  sd + Seq = sd
  Ap _n1 sd1 + Ap _n2 sd2 = mkCall Uω (sd1 ⊔ sd2)
  Sel dmds1 + Sel dmds2
    --- | and (Map.intersectionWith sameLength dmds1 dmds2) where sameLength = (==) `on` length
    = Sel (Map.unionWith (zipWithEqual (+)) dmds1 dmds2)

  _ + _ = Top
  _ * _ = error "unused"

instance Show SubDemand where
  show Seq = "Seq"
  show Top = "T"
  show (Ap n sd) = "Ap["++show n ++ ";" ++ show sd ++ "]"
  show (Sel kdss) = "Sel[" ++ concatMap single (Map.assocs kdss) ++ "]"
    where
      single (k, ds) = show k ++ "(" ++ showSep (showString ",") (map shows ds) ")"

instance Show Demand where
  show Abs = "A"
  show (n :* sd) = show n ++ "*" ++ show sd

type DmdEnv = Name :-> Demand

newtype DmdT a = DT { unDT :: Set Name -> SubDemand -> (a, DmdEnv) }
  deriving (Functor,Applicative,Monad) via ReaderT (Set Name) (ReaderT SubDemand (Writer DmdEnv))

type DmdD = DmdT DmdVal
data DmdVal = DmdFun Demand DmdVal | DmdNop | DmdBot

mkDmdFun :: Demand -> DmdVal -> DmdVal
mkDmdFun d v | d == topDmd, DmdNop <- v = DmdNop
             | d == absDmd, DmdBot <- v = DmdBot
             | otherwise                = DmdFun d v

instance Show DmdVal where
  show DmdBot = "\\bottom"
  show DmdNop = "\\bullet"
  show (DmdFun d v) = show d ++ "\\rightarrow" ++ show v

instance Eq DmdVal where
  DmdFun d1 v1 == DmdFun d2 v2 = d1 == d2 && v1 == v2
  DmdNop == DmdNop = True
  DmdNop == DmdFun d2 v2 = topDmd == d2 && DmdNop == v2
  DmdNop == DmdBot = False
  DmdBot == DmdBot = True
  DmdBot == DmdFun d2 v2 = absDmd == d2 && DmdBot == v2
  l      == r      = r == l

instance Lat DmdVal where
  bottom = DmdBot
  DmdNop ⊔ _ = DmdNop
  _ ⊔ DmdNop = DmdNop
  DmdBot ⊔ v = v
  v ⊔ DmdBot = v
  DmdFun d1 v1 ⊔ DmdFun d2 v2 = mkDmdFun (d1 ⊔ d2) (v1 ⊔ v2)

mapDmdEnv :: (DmdEnv -> DmdEnv) -> DmdT v -> DmdT v
mapDmdEnv f (DT m) = DT $ \ns sd -> case m ns sd of (v,φ) -> (v, f φ)

instance Trace (DmdT v) where
  step (Lookup x) (DT m) = DT $ \ns sd ->
    let (a, φ) = m ns sd in (a, φ + ext emp x (U1 :* sd))
  step _ τ = τ

isProd :: Tag -> Bool
isProd Pair = True
isProd _    = False -- TT,FF,Some,None,S,Z

squeezeSubDmd :: Set Name -> DmdD -> SubDemand -> DmdEnv
squeezeSubDmd ns (DT f) sd = snd (f ns sd)

squeezeDmd :: Set Name -> DmdD -> Demand -> DmdEnv
squeezeDmd _  _ Abs = emp
squeezeDmd ns d (n :* sd)
  | U1 <- n = squeezeSubDmd ns d sd
  | Uω <- n = squeezeSubDmd ns d sd + squeezeSubDmd ns d Seq
  | otherwise = error "UNonAbs"

fresh :: Set Name -> (Name, Set Name)
fresh ns = (x, Set.insert x ns) where x = "X" ++ show (Set.size ns)

freshs :: Int -> Set Name -> ([Name], Set Name)
freshs n ns = (xs, foldr Set.insert ns xs) where xs = take n (map (("X" ++) . show) [Set.size ns ..])

instance Domain (DmdT DmdVal) where
  stuck = return DmdBot
  fun _ _ f = DT $ \ns sd ->
    let (x,ns') = fresh ns in
    let proxy = step (Lookup x) (pure DmdNop) in
    let (n,sd') = case sd of
          Ap n sd' -> (n, sd')
          Seq        -> (U0, Seq)
          _          -> (Uω, Top) in
    if n == U0
      then (DmdBot, emp)
      else
        let (v,φ)  = unDT (f proxy) ns' sd' in
        let (d,φ') = (Map.findWithDefault absDmd x φ,Map.delete x φ) in
        (multDmdVal n (mkDmdFun d v), n * φ')
  con _ k ds = DT $ \ns sd ->
    let seq_dmds = replicate (length ds) absDmd
        top_dmds = replicate (length ds) topDmd
        dmds = case sd of
          Sel kdss -> case Map.lookup k kdss of
            Nothing                              -> seq_dmds
            Just dmds | length dmds == length ds -> dmds
                      | otherwise                -> top_dmds
          Seq -> seq_dmds
          _   -> top_dmds in
    (DmdNop, foldr (+) emp (zipWith (squeezeDmd ns) ds dmds))
  apply (DT f) arg = DT $ \ns sd ->
    case f ns (Ap U1 sd) of
      (DmdFun dmd v', φ) -> (v',     φ + squeezeDmd ns arg dmd)
      (DmdNop       , φ) -> (DmdNop, φ + squeezeDmd ns arg topDmd)
      (DmdBot       , φ) -> (DmdBot, φ + emp)
  select (DT scrut) fs = DT $ \ns sd -> case Map.assocs fs of
    [(k,f)] | k == Pair ->
      let (xs,ns')  = freshs (conArity k) ns in
      let proxies   = map (\x -> step (Lookup x) (pure DmdNop)) xs in
      let (v,φ)     = unDT (f proxies) ns' sd in
      let (ds,φ')   = (map (\x -> Map.findWithDefault absDmd x φ) xs,foldr Map.delete φ xs) in
      case scrut ns (mkSingleScrut k ds) of
        (_v,φ'') -> (v,φ''+φ')
    fs ->
      let (_v,φ) = scrut ns Top in
      let (v,φ') = lub (map (alt ns sd) fs) in
      (v, φ+φ')
      where
        alt ns sd (k,f) =
          let (xs,ns')  = freshs (conArity k) ns in
          let proxies   = map (\_ -> pure DmdNop) xs in
          let (v,φ)     = unDT (f proxies) ns' sd in
          let φ'        = foldr Map.delete φ xs in
          (v,φ')

-- | Very hacky way to see the arity of a function
arity :: Set Name -> DmdD -> Int
arity ns (DT m) = go 0
  where
    go n
      | n > 100                       = n
      | φ /= emp                      = n
      | v /= DmdBot                   = n
      | otherwise                     = go (n Prelude.+ 1)
      where
        sd = iterate (Ap U1) Seq !! n
        (v,φ) = m ns sd

nopD' :: DmdD
nopD' = DT $ \_ _ -> (DmdNop, emp)

peelManyCalls :: Int -> SubDemand -> (U, SubDemand)
peelManyCalls 0 sd = (U1,sd)
peelManyCalls _ Seq = (U0, Seq)
peelManyCalls _ Top = (Uω, Top)
peelManyCalls _ Sel{} = (Uω, Top)
peelManyCalls n (Ap u sd) | (u',sd') <- peelManyCalls (n-1) sd = (u * u', sd')

multDmdVal :: U -> DmdVal -> DmdVal
multDmdVal U0 _ = DmdNop
multDmdVal Uω (DmdFun d v) = mkDmdFun (d+d) (multDmdVal Uω v)
multDmdVal _  v = v

type DmdSummary = (DmdVal, DmdEnv)

concDmdSummary :: Int -> DmdSummary -> DmdD
concDmdSummary arty (v,φ) = DT $ \_ns sd ->
  let (u,_body_sd) = peelManyCalls arty sd in
  (multDmdVal u v, u * φ)


-- | A single call with n args in an otherwise unknown context
callSd :: Int -> SubDemand
callSd arity = iterate (Ap U1) Top !! arity

absDmdSummary :: Int -> Set Name -> DmdD -> DmdSummary
absDmdSummary arty ns (DT d) = d ns (callSd arty)

instance HasBind DmdD where
  bind _x rhs body = DT $ \ns sd ->
    let arty = arity ns (rhs nopD') in
--    if trace (show arty) arty == 0
    if arty == 0
      then
        let (x,ns') = fresh ns in
        let proxy = step (Lookup x) (pure DmdNop) in
        case unDT (body proxy) ns' sd of -- LetUp
          (v,φ) ->
            case Map.findWithDefault absDmd x φ of
              Abs -> (v,Map.delete x φ)
              _n :* sd -> let (_sd2,_v2,φ2) = kleeneFix (letup x rhs ns' sd) in (v,Map.delete x (φ + φ2))
      else
        let d1 = concDmdSummary arty (kleeneFix (absDmdSummary arty ns . rhs . concDmdSummary arty)) in
        unDT (body d1) ns sd
    where
      letup x rhs ns' sd (sd',v,_φ) =
        let sd'' = sd ⊔ sd' in
        case unDT (rhs (step (Lookup x) (pure v))) ns' sd'' of
          (v',φ') ->
            case Map.findWithDefault absDmd x φ' of
              Abs -> (sd'',v',φ')
              _n :* sd''' -> (sd'' ⊔ sd''',v',φ')

runDmd :: SubDemand -> DmdD -> (DmdVal, DmdEnv)
runDmd sd (DT d) = d Set.empty sd

anyCtx :: String -> (DmdVal, DmdEnv)
anyCtx s = runDmd Top $ eval (read s) emp

call :: Int -> String -> (DmdVal, DmdEnv)
call n s = runDmd (callSd n) $ eval (read s) emp

{-
>>> call 1 "let id = λx.x in id"

-- >>> call 2 "let const = λx.λy.y in const"
-}
