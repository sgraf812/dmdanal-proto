{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Order where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

class Eq a => Lat a where
  bottom :: a
  (⊔) :: a -> a -> a;

(⊑) :: Lat a => a -> a -> Bool
x ⊑ y = x ⊔ y == y

lub :: (Foldable f, Lat a) => f a -> a
lub = foldr (⊔) bottom
{-# INLINE lub #-}

instance (Ord k, Lat v) => Lat (Map k v) where
  bottom = Map.empty
  (⊔) = Map.unionWith (⊔)

instance (Ord a, Lat a) => Lat (Set a) where
  bottom = Set.empty
  (⊔) = Set.union

instance (Lat a, Lat b) => Lat (a,b) where
  bottom = (bottom,bottom)
  (a1,b1) ⊔ (a2,b2) = (a1⊔a2,b1⊔b2)

instance (Lat a, Lat b, Lat c) => Lat (a,b,c) where
  bottom = (bottom,bottom,bottom)
  (a1,b1,c1) ⊔ (a2,b2,c2) = (a1⊔a2,b1⊔b2,c1⊔c2)

kleeneFixFrom :: Lat a => a -> (a -> a) -> a
kleeneFixFrom bot f = stationary $ iterate f bot where stationary (a:b:r) = if b ⊑ a then b else stationary (b:r)

kleeneFix :: Lat a => (a -> a) -> a
kleeneFix = kleeneFixFrom bottom

kleeneFixFromM :: (Monad m, Lat a) => a -> (m a -> m a) -> m a
kleeneFixFromM a f = f (return a) >>= \b -> if a ⊑ b then return a else kleeneFixFromM b f

