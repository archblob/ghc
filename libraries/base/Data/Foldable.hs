{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE Trustworthy #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Foldable
-- Copyright   :  Ross Paterson 2005
-- License     :  BSD-style (see the LICENSE file in the distribution)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Class of data structures that can be folded to a summary value.
--
-----------------------------------------------------------------------------

module Data.Foldable (
    -- * Folds
    Foldable(..),
    -- ** Special biased folds
    foldrM,
    foldlM,
    -- ** Folding actions
    -- *** Applicative actions
    traverse_,
    for_,
    sequenceA_,
    asum,
    -- *** Monadic actions
    mapM_,
    forM_,
    sequence_,
    msum,
    -- ** Specialized folds
    concat,
    concatMap,
    and,
    or,
    any,
    all,
    maximumBy,
    minimumBy,
    -- ** Searches
    notElem,
    find
    ) where

import Data.Bool
import Data.Either
import Data.Eq
import qualified GHC.List as List
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Proxy

import GHC.Arr  ( Array(..), Ix(..), elems )
import GHC.Base hiding ( foldr )
import GHC.Num  ( Num(..) )

infix  4 `elem`, `notElem`

-- | Data structures that can be folded.
--
-- For example, given a data type
--
-- > data Tree a = Empty | Leaf a | Node (Tree a) a (Tree a)
--
-- a suitable instance would be
--
-- > instance Foldable Tree where
-- >    foldMap f Empty = mempty
-- >    foldMap f (Leaf x) = f x
-- >    foldMap f (Node l k r) = foldMap f l `mappend` f k `mappend` foldMap f r
--
-- This is suitable even for abstract types, as the monoid is assumed
-- to satisfy the monoid laws.  Alternatively, one could define @foldr@:
--
-- > instance Foldable Tree where
-- >    foldr f z Empty = z
-- >    foldr f z (Leaf x) = f x z
-- >    foldr f z (Node l k r) = foldr f (f k (foldr f z r)) l
--
class Foldable t where
    {-# MINIMAL foldMap | foldr #-}

    -- | Combine the elements of a structure using a monoid.
    fold :: Monoid m => t m -> m
    fold = foldMap id

    -- | Map each element of the structure to a monoid,
    -- and combine the results.
    foldMap :: Monoid m => (a -> m) -> t a -> m
    foldMap f = foldr (mappend . f) mempty

    -- | Right-associative fold of a structure.
    --
    -- @'foldr' f z = 'Prelude.foldr' f z . 'toList'@
    foldr :: (a -> b -> b) -> b -> t a -> b
    foldr f z t = appEndo (foldMap (Endo . f) t) z

    -- | Right-associative fold of a structure,
    -- but with strict application of the operator.
    foldr' :: (a -> b -> b) -> b -> t a -> b
    foldr' f z0 xs = foldl f' id xs z0
      where f' k x z = k $! f x z

    -- | Left-associative fold of a structure.
    --
    -- @'foldl' f z = 'Prelude.foldl' f z . 'toList'@
    foldl :: (b -> a -> b) -> b -> t a -> b
    foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

    -- | Left-associative fold of a structure.
    -- but with strict application of the operator.
    --
    -- @'foldl' f z = 'List.foldl'' f z . 'toList'@
    foldl' :: (b -> a -> b) -> b -> t a -> b
    foldl' f z0 xs = foldr f' id xs z0
      where f' x k z = k $! f z x

    -- | A variant of 'foldr' that has no base case,
    -- and thus may only be applied to non-empty structures.
    --
    -- @'foldr1' f = 'Prelude.foldr1' f . 'toList'@
    foldr1 :: (a -> a -> a) -> t a -> a
    foldr1 f xs = fromMaybe (error "foldr1: empty structure")
                    (foldr mf Nothing xs)
      where
        mf x m = Just (case m of
                         Nothing -> x
                         Just y  -> f x y)

    -- | A variant of 'foldl' that has no base case,
    -- and thus may only be applied to non-empty structures.
    --
    -- @'foldl1' f = 'Prelude.foldl1' f . 'toList'@
    foldl1 :: (a -> a -> a) -> t a -> a
    foldl1 f xs = fromMaybe (error "foldl1: empty structure")
                    (foldl mf Nothing xs)
      where
        mf m y = Just (case m of
                         Nothing -> y
                         Just x  -> f x y)

    -- | List of elements of a structure.
    toList :: t a -> [a]
    {-# INLINE toList #-}
    toList t = build (\ c n -> foldr c n t)

    -- | Test whether the structure is empty.
    null :: t a -> Bool
    null = foldr (\_ _ -> False) True

    -- | Returns the size/length of a finite structure as an 'Int'.
    length :: t a -> Int
    length = foldl' (\c _ -> c+1) 0

    -- | Does the element occur in the structure?
    elem :: Eq a => a -> t a -> Bool
    elem = any . (==)

    -- | The largest element of a non-empty structure.
    maximum :: Ord a => t a -> a
    maximum = foldr1 max

    -- | The least element of a non-empty structure.
    minimum :: Ord a => t a -> a
    minimum = foldr1 min

    -- | The 'sum' function computes the sum of the numbers of a structure.
    sum :: Num a => t a -> a
    sum = getSum . foldMap Sum

    -- | The 'product' function computes the product of the numbers of a
    -- structure.
    product :: Num a => t a -> a
    product = getProduct . foldMap Product

-- instances for Prelude types

instance Foldable Maybe where
    foldr _ z Nothing = z
    foldr f z (Just x) = f x z

    foldl _ z Nothing = z
    foldl f z (Just x) = f z x

instance Foldable [] where
    elem    = List.elem
    foldl   = List.foldl
    foldl'  = List.foldl'
    foldl1  = List.foldl1
    foldr   = List.foldr
    foldr1  = List.foldr1
    length  = List.length
    maximum = List.maximum
    minimum = List.minimum
    null    = List.null
    product = List.product
    sum     = List.sum
    toList  = id

instance Foldable (Either a) where
    foldMap _ (Left _) = mempty
    foldMap f (Right y) = f y

    foldr _ z (Left _) = z
    foldr f z (Right y) = f y z

instance Foldable ((,) a) where
    foldMap f (_, y) = f y

    foldr f z (_, y) = f y z

instance Ix i => Foldable (Array i) where
    foldr f z = List.foldr f z . elems
    foldl f z = List.foldl f z . elems
    foldr1 f = List.foldr1 f . elems
    foldl1 f = List.foldl1 f . elems

instance Foldable Proxy where
    foldMap _ _ = mempty
    {-# INLINE foldMap #-}
    fold _ = mempty
    {-# INLINE fold #-}
    foldr _ z _ = z
    {-# INLINE foldr #-}
    foldl _ z _ = z
    {-# INLINE foldl #-}
    foldl1 _ _ = error "foldl1: Proxy"
    {-# INLINE foldl1 #-}
    foldr1 _ _ = error "foldr1: Proxy"
    {-# INLINE foldr1 #-}

-- | Monadic fold over the elements of a structure,
-- associating to the right, i.e. from right to left.
foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
foldrM f z0 xs = foldl f' return xs z0
  where f' k x z = f x z >>= k

-- | Monadic fold over the elements of a structure,
-- associating to the left, i.e. from left to right.
foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
foldlM f z0 xs = foldr f' return xs z0
  where f' x k z = f z x >>= k

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
traverse_ :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

-- | 'for_' is 'traverse_' with its arguments flipped.
for_ :: (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
{-# INLINE for_ #-}
for_ = flip traverse_

-- | Map each element of a structure to a monadic action, evaluate
-- these actions from left to right, and ignore the results.
mapM_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
mapM_ f = foldr ((>>) . f) (return ())

-- | 'forM_' is 'mapM_' with its arguments flipped.
forM_ :: (Foldable t, Monad m) => t a -> (a -> m b) -> m ()
{-# INLINE forM_ #-}
forM_ = flip mapM_

-- | Evaluate each action in the structure from left to right,
-- and ignore the results.
sequenceA_ :: (Foldable t, Applicative f) => t (f a) -> f ()
sequenceA_ = foldr (*>) (pure ())

-- | Evaluate each monadic action in the structure from left to right,
-- and ignore the results.
sequence_ :: (Foldable t, Monad m) => t (m a) -> m ()
sequence_ = foldr (>>) (return ())

-- | The sum of a collection of actions, generalizing 'concat'.
asum :: (Foldable t, Alternative f) => t (f a) -> f a
{-# INLINE asum #-}
asum = foldr (<|>) empty

-- | The sum of a collection of actions, generalizing 'concat'.
msum :: (Foldable t, MonadPlus m) => t (m a) -> m a
{-# INLINE msum #-}
msum = foldr mplus mzero

-- These use foldr rather than foldMap to avoid repeated concatenation.

-- | The concatenation of all the elements of a container of lists.
concat :: Foldable t => t [a] -> [a]
concat = fold

-- | Map a function over all the elements of a container and concatenate
-- the resulting lists.
concatMap :: Foldable t => (a -> [b]) -> t a -> [b]
concatMap = foldMap

-- | 'and' returns the conjunction of a container of Bools.  For the
-- result to be 'True', the container must be finite; 'False', however,
-- results from a 'False' value finitely far from the left end.
and :: Foldable t => t Bool -> Bool
and = getAll . foldMap All

-- | 'or' returns the disjunction of a container of Bools.  For the
-- result to be 'False', the container must be finite; 'True', however,
-- results from a 'True' value finitely far from the left end.
or :: Foldable t => t Bool -> Bool
or = getAny . foldMap Any

-- | Determines whether any element of the structure satisfies the predicate.
any :: Foldable t => (a -> Bool) -> t a -> Bool
any p = getAny . foldMap (Any . p)

-- | Determines whether all elements of the structure satisfy the predicate.
all :: Foldable t => (a -> Bool) -> t a -> Bool
all p = getAll . foldMap (All . p)

-- | The largest element of a non-empty structure with respect to the
-- given comparison function.
maximumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a
maximumBy cmp = foldr1 max'
  where max' x y = case cmp x y of
                        GT -> x
                        _  -> y

-- | The least element of a non-empty structure with respect to the
-- given comparison function.
minimumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a
minimumBy cmp = foldr1 min'
  where min' x y = case cmp x y of
                        GT -> y
                        _  -> x

-- | 'notElem' is the negation of 'elem'.
notElem :: (Foldable t, Eq a) => a -> t a -> Bool
notElem x = not . elem x

-- | The 'find' function takes a predicate and a structure and returns
-- the leftmost element of the structure matching the predicate, or
-- 'Nothing' if there is no such element.
find :: Foldable t => (a -> Bool) -> t a -> Maybe a
find p = listToMaybe . concatMap (\ x -> if p x then [x] else [])

