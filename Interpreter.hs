{-#  OPTIONS_GHC -Wno-simplifiable-class-constraints  #-}
{-#  LANGUAGE DerivingStrategies  #-}
{-#  LANGUAGE DerivingVia  #-}
{-#  LANGUAGE PartialTypeSignatures  #-}
{-#  LANGUAGE LambdaCase  #-}
{-#  LANGUAGE QuantifiedConstraints  #-}
{-#  LANGUAGE UndecidableInstances  #-}

module Interpreter where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Text.Show (showListWith)
import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.State
import Exp

instance {-#  OVERLAPPING  #-} Show (Maybe (Value τ)) where
  show Nothing = "\\bot"
  show (Just a) = "\\mathtt{Just}(" ++ show a ++ ")"
instance {-#  OVERLAPPING  #-} Show (Identity (Value (ByName Identity))) where
  show (Identity a) = "\\langle " ++ show a ++ "\\rangle "
instance Show Event where
  show (Lookup x) = "\\LookupT(" ++ x ++ ")"
  show App1 = "\\AppIT"
  show App2 = "\\AppET"
  show Case1 = "\\CaseIT"
  show Case2 = "\\CaseET"
  show Let0 = "\\LetOT"
  show Let1 = "\\LetIT"
  show Update = "\\UpdateT"
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret a) = "\\langle "++show a++"\\rangle "
instance {-#  OVERLAPPING  #-} Show a => Show (T (Maybe a)) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret Nothing)  = "..."
  show (Ret (Just a)) = "\\langle "++show a++"\\rangle "
instance Show (Value τ) where
  show (Fun _) = "\\lambda"
  show (Con k _) = "\\mathit{Con}(" ++ show k ++ ")"
  show Stuck = "\\lightning"
instance (Show (τ v)) => Show (ByName τ v) where
  show (ByName τ) = show τ
instance Show (ByNeed τ a) where
  show _ = "\\wild"
instance (Show (τ v)) => Show (ByValue τ v) where
  show (ByValue τ) = show τ
instance (Show (τ v)) => Show (ByVInit τ v) where
  show (ByVInit _) = "\\wild"
instance (Show a, forall a. Show a => Show (τ a)) => Show (Fork (ParT τ) a) where
  show Empty = "Empty"
  show (Single a) = show a
  show (Fork l r) = "Fork(" ++ show l ++ "," ++ show r ++ ")"
instance (Show a, forall a. Show a => Show (m a)) => Show (ParT m a) where
  show (ParT m) = show m
instance {-#  OVERLAPPING  #-} (Show v) => Show (Addr :-> v) where
  showsPrec _ = showListWith (\(k,v) -> shows k . showString "\\!\\! \\mapsto \\!\\! " . shows v) . Map.toList
instance {-#  OVERLAPPING  #-} (Show v) => Show (Name :-> v) where
  showsPrec _ = showListWith (\(k,v) -> showString "\\mathit{" . showString k . showString "} \\! \\mapsto \\! " . shows v) . Map.toList

takeT :: Int -> T a -> T (Maybe a)
takeT 0 _ = return Nothing
takeT _ (Ret a) = return (Just a)
takeT n (Step e t) = Step e (takeT (n-1) t)

takeName :: Int -> ByName T a -> T (Maybe a)
takeName n (ByName τ) = takeT n τ
type (:->) = Map; emp :: Ord k => k :-> v
ext :: Ord k => (k :-> v) -> k -> v -> (k :-> v)
exts :: Ord k  => (k :-> v) -> [k] -> [v]
               -> (k :-> v)
(!) :: Ord k => (k :-> v) -> k -> v
dom :: Ord k => (k :-> v) -> Set k
(∈) :: Ord k => k -> Set k -> Bool
(<<) :: (b -> c) -> (a :-> b) -> (a :-> c)
assocs :: (k :-> v) -> [(k,v)]
emp = Map.empty
ext ρ x d = Map.insert x d ρ
exts ρ xs ds = foldl' (uncurry . ext) ρ (zip xs ds)
singenv x d = Map.singleton x d
(<<) = Map.map
infixr 9 <<
(!) = (Map.!)
dom = Map.keysSet
(∈) = Set.member
assocs = Map.assocs
type D τ = τ (Value τ);   type DName = D T
data T v = Step Event (T v) | Ret v
data Event  =  Lookup Name | Update | App1 | App2
            |  Let0 | Let1 | Case1 | Case2
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
instance Functor T where
  fmap f (Ret a) = Ret (f a)
  fmap f (Step e t) = Step e (fmap f t)
instance Applicative T where
  pure = Ret
  (<*>) = ap
instance Monad T where
  Ret v >>= k = k v
  Step e τ >>= k = Step e (τ >>= k)
eval  ::  (Trace d, Domain d, HasBind d)
      =>  Exp -> (Name :-> d) -> d
eval e ρ = case e of
  Var x  | x ∈ dom ρ  -> ρ ! x
         | otherwise  -> stuck
  Lam x body -> fun x $ \d ->
    step App2 (eval body ((ext ρ x d)))
  App e x  | x ∈ dom ρ  -> step App1 $
               apply (eval e ρ) (ρ ! x)
           | otherwise  -> stuck
  Let x e1 e2 -> bind x
    (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
    (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1))))
  ConApp k xs
    | all (∈ dom ρ) xs, length xs == conArity k
    -> con k (map (ρ !) xs)
    | otherwise
    -> stuck
  Case e alts -> step Case1 $
    select (eval e ρ) (cont << alts)
    where
       cont (xs, er) = (xs, f xs er)
       f xs er ds  |  length xs == length ds
                   =  step Case2 (eval er (exts ρ xs ds))
                   |  otherwise
                   =  stuck
class Trace d where
  step :: Event -> d -> d

class Domain d where
  stuck :: d
  fun :: Name -> (d -> d) -> d
  apply :: d -> d -> d
  con :: Tag -> [d] -> d
  select :: d -> (Tag :-> ([Name], [d] -> d)) ->  d

class HasBind d where
  bind :: Name -> (d -> d) -> (d -> d) -> d
instance Trace (T v) where
  step = Step

instance Monad τ => Domain (D τ) where
  stuck = return Stuck
  fun _ f = return (Fun f)
  apply  d a = d >>= \v -> case v of
    Fun f -> f a; _ -> stuck
  con k ds = return (Con k ds)
  select dv alts = dv >>= \v -> case v of
    Con k ds | k ∈ dom alts  -> snd (alts ! k) ds
    _                        -> stuck



evalName e ρ = eval e ρ :: D (ByName T)
newtype ByName τ v = ByName { unByName :: (τ v) }
  deriving newtype (Functor,Applicative,Monad)

instance Trace (τ v) => Trace (ByName τ v) where
  step e = ByName . step e . unByName

instance HasBind (D (ByName τ)) where
  bind _ rhs body = body (fix rhs)
evalNeed e ρ μ = unByNeed (eval e ρ :: D (ByNeed T)) μ

type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
newtype ByNeed τ v = ByNeed { unByNeed :: Heap (ByNeed τ) -> τ (v, Heap (ByNeed τ)) }

getN  :: Monad τ => ByNeed τ (Heap (ByNeed τ));         getN    = ByNeed (\ μ -> return (μ, μ))
putN  :: Monad τ => Heap (ByNeed τ) -> ByNeed τ ();    putN μ  = ByNeed (\ _ -> return ((), μ))


instance (forall v. Trace (τ v)) => Trace (ByNeed τ v) where step e m = ByNeed (step e . unByNeed m)

fetchN :: Monad τ => Addr -> D (ByNeed τ); fetchN a = getN >>= \μ -> μ ! a

memoN :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memoN a d = d >>= \v -> ByNeed (upd v)
  where  upd Stuck  μ = return (Stuck :: Value (ByNeed τ), μ)
         upd v      μ = step Update (return (v, ext μ a (memoN a (return v))))

instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByNeed τ)) where
  bind _ rhs body = do  μ <- getN
                        let a = nextFree μ
                        putN (ext μ a (memoN a (rhs (fetchN a))))
                        body (fetchN a)
nextFree h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

deriving via StateT (Heap (ByNeed τ)) τ instance Functor τ  => Functor (ByNeed τ)
deriving via StateT (Heap (ByNeed τ)) τ instance Monad τ    => Applicative (ByNeed τ)
deriving via StateT (Heap (ByNeed τ)) τ instance Monad τ    => Monad (ByNeed τ)
evalValue e ρ = eval e ρ :: D (ByValue T)

newtype ByValue τ v = ByValue { unByValue :: τ v }

instance Trace (τ v) => Trace (ByValue τ v) where
  step e (ByValue τ) = ByValue (step e τ)

class Extract τ where getValue :: τ v -> v
instance Extract T where getValue (Ret v) = v; getValue (Step _ τ) = getValue τ

instance (Trace (D (ByValue τ)), Monad τ, Extract τ) => HasBind (D (ByValue τ)) where
  bind _ rhs body = step Let0 (do  v1 <- d; body (return v1))
                                   where  d = rhs (return v)          :: D (ByValue τ)
                                          v = getValue (unByValue d)  :: Value (ByValue τ)
deriving instance Functor τ     => Functor (ByValue τ)
deriving instance Applicative τ => Applicative (ByValue τ)
deriving instance Monad τ       => Monad (ByValue τ)
evalVInit e ρ μ = unByVInit (eval e ρ :: D (ByVInit T)) μ

newtype ByVInit τ v = ByVInit { unByVInit :: Heap (ByVInit τ) -> τ (v, Heap (ByVInit τ)) }
instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByVInit τ)) where
  bind _ rhs body = do  μ <- getV
                        let a = nextFree μ
                        putV (ext μ a stuck)
                        step Let0 (memoV a (rhs (fetchV a))) >>= body . return
deriving via StateT (Heap (ByVInit τ)) τ instance Functor τ  => Functor (ByVInit τ)
deriving via StateT (Heap (ByVInit τ)) τ instance Monad τ    => Applicative (ByVInit τ)
deriving via StateT (Heap (ByVInit τ)) τ instance Monad τ    => Monad (ByVInit τ)

getV :: Monad τ => ByVInit τ (Heap (ByVInit τ))
getV = ByVInit (\ μ -> return (μ, μ))
putV :: Monad τ => Heap (ByVInit τ) -> ByVInit τ ()
putV μ = ByVInit (\ _ -> return ((), μ))

instance (forall v. Trace (τ v)) => Trace (ByVInit τ v) where step e m = ByVInit (step e . unByVInit m)

fetchV :: Monad τ => Addr -> D (ByVInit τ)
fetchV a = getV >>= \μ -> μ ! a

memoV :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByVInit τ) -> D (ByVInit τ)
memoV a d = d >>= \v -> ByVInit (upd v)
  where  upd Stuck  μ = return (Stuck :: Value (ByVInit τ), μ)
         upd v      μ = return (v, ext μ a (memoV a (return v)))
evalClair e ρ = runClair $ eval e ρ :: T (Value (Clairvoyant T))

data Fork f a = Empty | Single !a | Fork (f a) (f a)
  deriving Functor

newtype ParT τ a = ParT { unParT :: τ (Fork (ParT τ) a) }
  deriving Functor

instance Monad τ => Applicative (ParT τ) where
  pure a = ParT (pure (Single a))
  (<*>) = ap
instance Monad τ => Monad (ParT τ) where
  ParT mas >>= k = ParT $ mas >>= \case
    Empty -> pure Empty
    Single a -> unParT (k a)
    Fork l r -> pure (Fork (l >>= k) (r >>= k))
instance Monad τ => Alternative (ParT τ) where
  empty = ParT (pure Empty)
  l <|> r = ParT (pure (Fork l r))

newtype Clairvoyant τ a = Clairvoyant { unClair :: ParT τ a }
  deriving newtype (Functor,Applicative,Monad)

instance (forall v. Trace (τ v)) => Trace (Clairvoyant τ v) where
  step e (Clairvoyant (ParT mforks)) = Clairvoyant $ ParT $ step e mforks

leftT :: Monad τ => ParT τ a -> ParT τ a
leftT (ParT τ) = ParT $ τ >>= \case
  Fork l _ -> unParT l
  _ -> undefined

rightT :: Monad τ => ParT τ a -> ParT τ a
rightT (ParT τ) = ParT $ τ >>= \case
  Fork _ r -> unParT r
  _ -> undefined

parFix :: (Extract τ, Monad τ) => (Fork (ParT τ) a -> ParT τ a) -> ParT τ a
parFix f = ParT $ fix (unParT . f . getValue) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork _ _ -> pure (Fork (parFix (leftT . f)) (parFix (rightT . f)))

instance (Extract τ, Monad τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind _ rhs body = Clairvoyant (skip <|> let') >>= body
    where
      skip = return (Clairvoyant empty)
      let' = fmap return $ unClair $ step Let0 $ Clairvoyant $ parFix $ unClair . rhs . Clairvoyant . ParT . return

headParT :: (Monad τ, Extract τ) => ParT τ v -> τ (Maybe v)
headParT τ = go τ
  where
    go :: (Monad τ, Extract τ) => ParT τ v -> τ (Maybe v)
    go (ParT τ) = τ >>= \case
      Empty    -> pure Nothing
      Single a -> pure (Just a)
      Fork l r -> case getValue (go l) of
        Nothing -> go r
        Just _  -> go l

runClair :: (Monad τ, Extract τ) => D (Clairvoyant τ) -> τ (Value (Clairvoyant τ))
runClair (Clairvoyant m) = headParT m >>= \case
  Nothing -> error "There should have been at least one Clairvoyant trace"
  Just t  -> pure t
