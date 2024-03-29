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
import Debug.Trace
_ = trace

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
  = DmdBot                      -- ⊥
  | DmdFun Demand (DmdT DmdVal) -- λdmd.{x↦dmd}|>val
  | DmdCon (Tag :-> [DmdVal])   -- Con[K1(val,val,...); K2(val,val,...)]
  | DmdNop (Set Name)           -- end{fvs}

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
zipWithEqual f as bs = assertMsg (length as == length bs) "not same length" (zipWith f as bs)

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
-- Manipulating the semantic domain (SubDemand, Demand, DmdEnv, DmdVal)

absDmd, topDmd :: Demand
absDmd = Abs
topDmd = Uω :* Top

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

lookupSelDmds :: Tag -> SubDemand -> [Demand]
lookupSelDmds k Seq = replicate (conArity k) absDmd
lookupSelDmds k (Sel kdss) = case Map.lookup k kdss of
  Nothing                               -> replicate (conArity k) absDmd
  Just dmds | length dmds == conArity k -> dmds
            | otherwise                 -> replicate (conArity k) topDmd
lookupSelDmds k _ = replicate (conArity k) topDmd

topEnv :: Set Name -> DmdEnv
topEnv fvs = Map.fromSet (const topDmd) fvs

whnf :: DmdVal -> DmdD
whnf v = \_sd -> emp :|> v

mkDmdFun :: Demand -> DmdT DmdVal -> DmdVal
mkDmdFun d (φ :|> v) | d == topDmd, DmdNop fvs <- v, topEnv fvs == φ = v
                     | d == absDmd, all (== absDmd) φ, DmdBot <- v   = DmdBot
                     | otherwise                                     = DmdFun d (φ :|> v)

asDmdFun :: DmdVal -> (Demand, DmdEnv, DmdVal)
asDmdFun (DmdFun dmd (φ :|> v)) = (dmd, φ, v)
asDmdFun DmdBot                 = (absDmd, emp, DmdBot)
asDmdFun (DmdNop fvs)           = (topDmd, Map.fromSet (const topDmd) fvs, DmdNop Set.empty)
asDmdFun v@(DmdCon _)           = assert (null (valFVs v)) (topDmd, emp, DmdNop Set.empty) -- topDmd is conservative; could do absDmd

lookupDmdCon :: Tag -> DmdVal -> Maybe [DmdVal]
lookupDmdCon k (DmdCon kvs) = Map.lookup k kvs
lookupDmdCon k (DmdNop _)   = Just (replicate (conArity k) (DmdNop Set.empty)) -- TODO: Assert that DmdNop has no free vars
lookupDmdCon _ _ = Nothing -- DmdBot, DmdFun

squeezeSubDmd :: DmdT DmdVal -> SubDemand -> DmdEnv
squeezeSubDmd (φ :|> v) sd = φ + squeeze_val sd v
  where
    squeeze_val sd (DmdFun _ (φ :|> v))
      | (n,sd') <- asAp sd = n*φ + squeeze_val sd' v
    squeeze_val _ _ = emp -- DmdNop, DmdBot, DmdCon. NB: DmdCon has no valFVs!!!

squeezeEnv :: DmdD -> Demand -> DmdEnv
-- Applied to free variable denotations in ρ.
-- DmdAnal maintains that every such ρ(x) looks like
-- `step (Lookup y) (whnf v)` for some variable `y` and value `v`.
-- This is important to understand the Uω case below.
squeezeEnv _ Abs = emp
squeezeEnv d (n :* sd)
  | U1 <- n = squeezeSubDmd (d sd) sd
  | Uω <- n = squeezeSubDmd (d Seq) Seq + squeezeSubDmd (d sd) sd
     -- See comment on squeezeEnv; `squeezeSubDmd (d Seq) Seq` will only
     -- add a (U1 :* Seq) demand on the variable `y`, because the rest
     -- of the DmdD is in WHNF (`whnf v`).
     -- The second `squeezeSubDmd (d sd) sd` will then add (U1 :* sd) on
     -- `y` as well as add uses from `v`.
  | otherwise = error "UNonAbs"

valueShell :: DmdD -> Demand -> DmdVal
-- It is `valFVs (valueShell d sd) == Set.empty`.
--
-- Important property: For all `d :: DmdD` and `dmd :: Demand`,
-- define `d' = squeezeEnv d dmd :|> valueShell d dmd`.
-- Then we have `squeezeEnv d dmd ⊑ squeezeEnv d' dmd`.
-- I.e., d' is a "squeezed" approximation of d, where all uses of free variables
-- are in the outer φ.
valueShell _ Abs       = DmdBot
valueShell d (_ :* sd) = case d sd of _ :|> v -> go v
  where
    go (DmdFun d (_ :|> v)) = DmdFun d (emp :|> go v)
    go (DmdCon dkvs)        = DmdCon (Map.map (map go) dkvs)
    go (DmdNop _)           = DmdNop Set.empty
    go DmdBot               = DmdBot

delFV :: Name -> DmdT DmdVal -> DmdT DmdVal
delFV x (φ :|> v) = Map.delete x φ :|> del_value v
  where
    del_value (DmdFun d τ) = mkDmdFun d (delFV x τ)
    del_value v = v

lookupDmdEnv :: Name -> DmdEnv -> Demand
lookupDmdEnv x φ = Map.findWithDefault absDmd x φ

--------------------------
-- Domain definition

mkProxy :: Name -> DmdVal -> DmdD
mkProxy x v = step (Lookup x) (whnf v)

instance Trace DmdD where
  step (Lookup x) m = \sd ->
    let φ :|> a = m sd in (φ + ext emp x (U1 :* sd)) :|> a
  step _ τ = τ

instance Domain DmdD where
  stuck = whnf DmdBot
  fun x f = \sd ->
    let (_n,sd') = asAp sd in -- _n is the one-shot annotation that goes on the lambda
    let τ = f (mkProxy x (DmdNop Set.empty)) sd' in
    let d = lookupDmdEnv x (squeezeSubDmd τ sd') in
    emp :|> mkDmdFun d (delFV x τ)
  con k ds = \sd ->
    let dmds = lookupSelDmds k sd in
    let φ = foldr (+) emp (zipWith squeezeEnv ds dmds) in
    φ :|> DmdCon (Map.singleton k (zipWith valueShell ds dmds))
  apply f_body arg = \sd ->
    let φ :|> v = f_body (Ap U1 sd) in
--    trace ("apply " ++ show (φ :|> v)) $
    let (dmd, φ', v') = asDmdFun v in
    (φ + φ' + squeezeEnv arg dmd) :|> v'
  select scrut fs = \sd ->
    let nop_fields (xs, _f) = map (const (DmdNop Set.empty)) xs in
    let nop_scrut_v = DmdCon (nop_fields << fs) in -- the worst case value
    let iter v_scrut =
          let φ' :|> (scrut_sd,v_rhss) = lub (map (alt v_scrut sd) (Map.assocs fs)) in
          let φ  :|> v_scrut' = scrut scrut_sd in
          (v_scrut', (φ+φ') :|> v_rhss) in
--    snd (iter nop_scrut_v) -- the regular version without a fixpoint; then we cannot know v_scrut'
    snd (iter (kleeneFixFrom nop_scrut_v (fst . iter)))
    where
      alt v_scrut sd (k,(xs,f_rhs)) = case lookupDmdCon k v_scrut of
        Nothing -> bottom -- dead code path; return bot
        Just vs ->
          let τ = f_rhs (zipWithEqual mkProxy xs vs) sd in
          let ds = let φ = squeezeSubDmd τ sd in
                   map (\x -> lookupDmdEnv x φ) xs in
          let φ :|> v = foldr delFV τ xs in
          φ :|> (mkSingleSel k ds, v)

instance HasBind DmdD where
  bind x rhs body = \sd ->
    let iter v_rhs =
          let τ_body            = body (whnf v_rhs) sd    -- NB: eval will wrap `step (Lookup x)` around `whnf v_rhs`, as in `mkProxy`
              φ_rhs :|>  v_rhs' = rhs  (whnf v_rhs) sd_x
              ds_x              = lookupDmdEnv x (squeezeSubDmd τ_body sd)
              (n_x, sd_x)       = case ds_x of Abs -> (U0, Seq); n :* sd -> (n,sd)
              oneify u          = if u == Uω then U1 else u -- `oneify u = glb U1 u = U1 ∩ u`
              φ_body :|> v_body = delFV x τ_body
          in -- trace ("bind " ++ x ++ ": " ++ show ds_x ++ ", " ++ show v_rhs' ++ ", " ++ show τ_body)
             (v_rhs', v_body, φ_body + (oneify n_x * φ_rhs))
        fstOf3 (a,_,_) = a
    in case iter (kleeneFix (fstOf3 . iter)) of (_v_rhs, v, φ) -> φ :|> v

----------------------------------
-- Entrypoints

dmdAnal :: Exp -> DmdD
dmdAnal e = eval e initialEnv
  where
    initialEnv = Map.fromSet (\x -> mkProxy x (DmdNop Set.empty)) (freeVars e)


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
  DmdBot == DmdBot = True
  DmdFun d1 τ1 == DmdFun d2 τ2 = d1 == d2 && τ1 == τ2
  DmdCon dkvs1 == DmdCon dkvs2 = dkvs1 == dkvs2
  DmdNop fvs1 == DmdNop fvs2 = fvs1 == fvs2
  _      == _      = False

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
  show (DmdNop fvs) = "end" ++ if Set.null fvs then "" else showSet showString (Set.toList fvs) ""
  show (DmdFun d τ) = "λ" ++ show d ++ "." ++ show τ
  show (DmdCon dkvs) = "Con[" ++ showSep (showString ";") (map single (Map.assocs dkvs)) "]"
    where
      single (k, vs) = shows k . showString "(" . showSep (showString ",") (map shows vs) . showString ")"
