{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PatternSynonyms #-}
module DmdAnal where

import Prelude hiding ((+), (*))
import Exp
import Order
import Interpreter
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
-- import Debug.Trace

---------------------
-- Abstract domain

data U = U0 | U1 | Uω deriving (Eq, Ord)

type UNonAbs  = U -- Not U0
type UNonOnce = U -- Not U1

data Demand = Abs | UNonAbs :* SubDemand deriving Eq
data SubDemand
  = Seq                     -- Stop context
  | Top                     -- Uknown context
  | Ap UNonAbs SubDemand    -- Apply context
  | Sel (Tag :-> [Demand])  -- Select context

type DmdEnv = Name :-> Demand

newtype DmdT a = DmdT (DmdEnv, a) deriving (Eq, Lat) via (DmdEnv,a)
pattern φ :|> v = DmdT (φ, v)
{-# COMPLETE (:|>) #-}

data DmdVal
  = DmdBot
  | DmdFun Demand (DmdT DmdVal)
  | DmdCon (Tag :-> [DmdVal])
  | DmdNop (Set Name)

type DmdD = SubDemand -> DmdT DmdVal

-----------------
-- Algebra

class UVec a where
  (+)  :: a -> a -> a
  (*)  :: U -> a -> a
infixl 6 +
infixl 7 *

instance Lat U where
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω

instance UVec U where
  U1 + U1 = Uω
  u1 + u2 = u1 ⊔ u2
  U0 * _ = U0
  _ * U0 = U0
  U1 * u = u
  Uω * _ = Uω

zipWithEqual :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWithEqual f as bs | length as == length bs = zipWith f as bs
                     | otherwise              = error "not same length"

instance Lat Demand where
  bottom = Abs
  Abs ⊔ d = d
  d ⊔ Abs = d
  (u1:*sd1) ⊔ (u2:*sd2) = (u1⊔u2) :* (sd1⊔sd2)

instance UVec Demand where
  Abs + d = d
  d + Abs = d
  (_u1:*sd1) + (_u2:*sd2) = Uω :* (sd1+sd2)
  _ * Abs = Abs
  U0 * _ = Abs
  U1 * d = d
  Uω * (_ :* sd) = Uω :* (Uω * sd)

instance Lat SubDemand where
  bottom = Seq
  Top ⊔ _ = Top
  _ ⊔ Top = Top
  Seq ⊔ sd = sd
  sd ⊔ Seq = sd
  Ap n1 sd1 ⊔ Ap n2 sd2 = mkAp (n1⊔n2) (sd1⊔sd2)
  Sel dmds1 ⊔ Sel dmds2
    = Sel (Map.unionWith (zipWithEqual (⊔)) dmds1 dmds2)
  _ ⊔ _ = Top

instance UVec SubDemand where
  Top + _ = Top
  _ + Top = Top
  Seq + sd = sd
  sd + Seq = sd
  Ap _n1 sd1 + Ap _n2 sd2 = mkAp Uω (sd1 ⊔ sd2)
  Sel dmds1 + Sel dmds2
    --- | and (Map.intersectionWith sameLength dmds1 dmds2) where sameLength = (==) `on` length
    = Sel (Map.unionWith (zipWithEqual (+)) dmds1 dmds2)
  _ + _ = Top
  U0 * _ = Seq
  U1 * sd = sd
  Uω * Ap n sd = mkAp (n+n) sd
  Uω * Sel dmds = Sel (Map.map (\dmds -> zipWith (+) dmds dmds) dmds)
  Uω * sd = sd

instance (Ord k, UVec u) => UVec (k :-> u) where
  (+) = Map.unionWith (+)
  u * m = Map.map (u *) m

valFVs :: DmdVal -> Set Name
valFVs DmdBot = Set.empty
valFVs (DmdNop fvs) = fvs
valFVs (DmdFun _ (φ :|> v)) = dom φ `Set.union` valFVs v
valFVs (DmdCon kvs) = foldr (Set.union . Set.unions . map valFVs) Set.empty kvs

instance Lat DmdVal where
  bottom = DmdBot
  DmdNop fvs ⊔ v = DmdNop (fvs `Set.union` valFVs v)
  v ⊔ DmdNop fvs = DmdNop (fvs `Set.union` valFVs v)
  DmdBot ⊔ v = v
  v ⊔ DmdBot = v
  DmdFun d1 τ1 ⊔ DmdFun d2 τ2 = mkDmdFun (d1 ⊔ d2) (τ1 ⊔ τ2)
  DmdCon dkvs1 ⊔ DmdCon dkvs2 = DmdCon (Map.unionWith (zipWithEqual (⊔)) dkvs1 dkvs2)
  v1 ⊔ v2 = DmdNop (valFVs v1 `Set.union` valFVs v2)

---------------------------
-- (Smart) Constructors

mkAp :: U -> SubDemand -> SubDemand
mkAp U0 _   = Seq
mkAp Uω Top = Top
mkAp n  sd  = Ap n sd

asAp :: SubDemand -> (U, SubDemand)
asAp (Ap n sd) = (n, sd)
asAp Seq       = (U0, Seq)
asAp _         = (Uω, Top)

-- | A single call with n args in an otherwise unknown context
callCtx :: Int -> SubDemand
callCtx arity = iterate (Ap U1) Top !! arity

mkSingleSel :: Tag -> [Demand] -> SubDemand
mkSingleSel k ds
  | all (== absDmd) ds = Seq
  | otherwise          = Sel (Map.singleton k ds)

absDmd, topDmd :: Demand
absDmd = Abs
topDmd = Uω :* Top

whnf :: DmdVal -> DmdD
whnf v = \_sd -> emp :|> v

topEnv :: Set Name -> DmdEnv
topEnv fvs = Map.fromSet (const topDmd) fvs

mkDmdFun :: Demand -> DmdT DmdVal -> DmdVal
mkDmdFun d (φ :|> v) | d == topDmd, all (== topDmd) φ, DmdNop fvs <- v, topEnv fvs == φ = DmdNop fvs
                     | d == absDmd, all (== absDmd) φ, DmdBot <- v                      = DmdBot
                     | otherwise                                                        = DmdFun d (φ :|> v)

--------------------------
-- Domain definition

instance Trace DmdD where
  step (Lookup x) m = \sd ->
    let φ :|> a = m sd in (φ + ext emp x (U1 :* sd)) :|> a
  step _ τ = τ

squeezeTSubDmd :: DmdT DmdVal -> SubDemand -> DmdEnv
squeezeTSubDmd (φ :|> v) sd = φ + squeeze_val sd v
  where
    squeeze_val sd (DmdFun _ (φ :|> v))
      | (n,sd') <- asAp sd = n*φ + squeeze_val sd' v
    squeeze_val _ _ = emp -- DmdNop, DmdBot, DmdCon. NB: DmdCon has no valFVs!!!

squeezeSubDmd :: DmdD -> SubDemand -> DmdEnv
squeezeSubDmd f sd = squeezeTSubDmd (f sd) sd

squeezeDmd :: DmdD -> Demand -> DmdEnv
squeezeDmd _ Abs = emp
squeezeDmd d (n :* sd)
  | U1 <- n = squeezeSubDmd d sd
  | Uω <- n = squeezeSubDmd d Seq + squeezeSubDmd d sd
  | otherwise = error "UNonAbs"

-- | We will have `valFVs (valueShell d sd) == Set.empty`.
valueShell :: DmdD -> Demand -> DmdVal
valueShell _ Abs       = DmdBot
valueShell d (_ :* sd) = case d sd of _ :|> v -> go v
  where
    go (DmdFun d (_ :|> v)) = DmdFun d (emp :|> go v)
    go (DmdCon dkvs)        = DmdCon (Map.map (map go) dkvs)
    go (DmdNop _)           = DmdNop Set.empty
    go DmdBot               = DmdBot

delFV :: DmdT DmdVal -> Name -> DmdT DmdVal
delFV (φ :|> v) x = Map.delete x φ :|> del_value v
  where
    del_value (DmdFun d τ) = mkDmdFun d (delFV τ x)
    del_value v = v

instance Domain DmdD where
  stuck = whnf DmdBot
  fun x f = \sd ->
    let proxy = step (Lookup x) (whnf (DmdNop Set.empty)) in
    let (_n,sd') = asAp sd in -- _n is the one-shot annotation
    let τ = f proxy sd' in
    let d = Map.findWithDefault absDmd x (squeezeTSubDmd τ sd') in
    emp :|> mkDmdFun d (delFV τ x)
  con k ds = \sd ->
    let seq_dmds = replicate (length ds) absDmd in
    let top_dmds = replicate (length ds) topDmd in
    let dmds = case sd of
          Sel kdss -> case Map.lookup k kdss of
            Nothing                              -> seq_dmds
            Just dmds | length dmds == length ds -> dmds
                      | otherwise                -> top_dmds
          Seq -> seq_dmds
          _   -> top_dmds in
    let φ = foldr (+) emp (zipWith squeezeDmd ds dmds) in
    φ :|> DmdCon (Map.singleton k (zipWith valueShell ds dmds))
  apply f arg = \sd ->
    case f (Ap U1 sd) of
      φ :|> DmdBot                 -> (φ + emp                    ) :|> DmdBot
      φ :|> DmdFun dmd (φ' :|> v') -> (φ + φ' + squeezeDmd arg dmd) :|> v'
      φ :|> v                      -> (φ + squeezeDmd arg topDmd  ) :|> DmdNop (valFVs v)
  select scrut fs = \sd ->
    let φ' :|> (scrut_sd,v) = lub (map (alt sd) (Map.assocs fs)) in
    let φ  :|> _v = scrut scrut_sd in -- TODO: fixpoint for value _v? Currently we say DmdNop for field denotations
    (φ+φ') :|> v
    where
      alt sd (k,(xs,f)) =
        let proxies   = map (\x -> step (Lookup x) (whnf (DmdNop Set.empty))) xs in
        let φ :|> v   = f proxies sd in
        let (ds,φ')   = (map (\x -> Map.findWithDefault absDmd x φ) xs,foldr Map.delete φ xs) in
        φ' :|> (mkSingleSel k ds, v)

instance HasBind DmdD where
  bind x rhs body = \sd ->
    let iter v_rhs =
          let proxy             = step (Lookup x) (whnf v_rhs)
              φ_body :|> v_body = body proxy sd
              φ_rhs :|>  v_rhs' = rhs  proxy sd_x
              (ds_x, φ_body')   = (Map.findWithDefault absDmd x φ_body, Map.delete x φ_body)
              (n_x, sd_x)       = case ds_x of Abs -> (U0, Seq); n :* sd -> (n,sd)
              oneify u          = if u == Uω then U1 else u
          in (v_rhs', v_body, φ_body' + (oneify n_x) * φ_rhs)
        fstOf3 (a,_,_) = a
    in case iter (kleeneFix (fstOf3 . iter)) of (_v_rhs, v, φ) -> φ :|> v

----------------------------------
-- Entrypoints

dmdAnal :: Exp -> DmdD
dmdAnal e = eval e initialEnv
  where
    initialEnv = Map.fromSet (\x -> step (Lookup x) (whnf (DmdNop Set.empty))) (freeVars e)


anyCtx :: String -> DmdT DmdVal
anyCtx s = dmdAnal (read s) Top

call :: Int -> String -> DmdT DmdVal
call n s = dmdAnal (read s) (callCtx n)

{-
>>> call 1 "let id = λx.x in id"

-- >>> call 2 "let const = λx.λy.y in const"
--
>>> call 2 "λx.λy.case y of { Some(z) -> z x; Pair(a,b) -> a b }"
-}

----------------------------------
-- Boring stuff:

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

instance Eq DmdVal where
  DmdFun d1 τ1 == DmdFun d2 τ2 = d1 == d2 && τ1 == τ2
  DmdNop fvs1 == DmdNop fvs2 = fvs1 == fvs2
  DmdNop fvs == DmdFun d2 (φ2 :|> v2) = topDmd == d2 && φ2 == topEnv fvs && DmdNop fvs == v2
  DmdNop _ == DmdBot = False
  DmdBot == DmdBot = True
  DmdBot == DmdFun d2 (φ2 :|> v2) = absDmd == d2 && Map.null φ2 && DmdBot == v2
  l      == r      = r == l

instance Show U where
  show U0 = "0"
  show U1 = "1"
  show Uω = "ω"

instance Show SubDemand where
  show Seq = "HU"
  show Top = "U"
  show (Ap n sd) = "Ap["++show n ++ ";" ++ show sd ++ "]"
  show (Sel kdss) = "Sel[" ++ showSep (showString ";") (map single (Map.assocs kdss)) "]"
    where
      single (k, ds) = shows k . showString "(" . showSep (showString ",") (map shows ds) . showString ")"

instance Show Demand where
  show Abs = "A"
  show (n :* sd) = show n ++ "*" ++ show sd

instance {-#  OVERLAPPING  #-} Show DmdEnv where
  showsPrec _ = showSet (\(k,v) -> showString k . showString "↦" . shows v) . Map.toList
showSet :: (a -> ShowS) ->  [a] -> ShowS
showSet _     []     s = "{}" ++ s
showSet showx (x:xs) s = '{' : showx x (showl xs)
  where
    showl []     = '}' : s
    showl (y:ys) = ',' : showx y (showl ys)

instance Show v => Show (DmdT v) where
  show (φ :|> v) = show φ ++ "|>" ++ show v

instance Show DmdVal where
  show DmdBot = "⊥"
  show (DmdNop fvs) = "." ++ if Set.null fvs then "" else show fvs
  show (DmdFun d τ) = "λ" ++ show d ++ "." ++ show τ
  show (DmdCon dkvs) = "Con[" ++ showSep (showString ";") (map single (Map.assocs dkvs)) "]"
    where
      single (k, vs) = shows k . showString "(" . showSep (showString ",") (map shows vs) . showString ")"
