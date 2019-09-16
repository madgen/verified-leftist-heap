#!/usr/bin/env stack
-- stack script --resolver lts-14.5 --package QuickCheck --ghc-options -Wall

{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

module HeapLeftistTyped
  ( main
  , Heap(..)
  , VanillaHeap, SafeHeap, SaferHeap
  ) where

import Data.Kind (Type)
import Data.Foldable (foldlM)

import Test.QuickCheck
import Test.QuickCheck.Modifiers (Positive(..))
import Test.QuickCheck.Gen (sample')

class Heap heap where
  {-# MINIMAL
    isEmpty, empty,
    (singleton | insert),
    (merge | insert),
    (decompose | (findMax, deleteMax))
    #-}

  type Elem heap

  -- Predicates
  isEmpty :: heap -> Bool

  -- Access
  findMax :: heap -> Maybe (Elem heap)
  findMax = fmap fst <$> decompose

  -- Creation
  empty :: heap

  singleton :: Elem heap -> heap
  singleton = (`insert` empty)

  fromList :: [ Elem heap ] -> heap
  fromList xs = -- O(n) for leftist heaps
    case go (map singleton xs) of
      [ heap ] -> heap
      [ ]      -> empty
      _        -> error "Impossible. Did not converge to a single heap."
    where
    go [] = []
    go [ x ] = [ x ]
    go (x : y : rest) = go (merge x y : go rest)

  -- Motification
  insert :: Elem heap -> heap -> heap
  insert x = merge (singleton x)

  merge :: heap -> heap -> heap
  heap1 `merge` heap2 =
    case decompose heap1 of
      Just (heapMax, heapRest) -> heapRest `merge` (heapMax `insert` heap2)
      Nothing                  -> heap2

  decompose :: heap -> Maybe (Elem heap, heap)
  decompose heap =
    case (findMax heap, deleteMax heap) of
      (Just heapMax, Just heapRest) -> Just (heapMax, heapRest)
      (Nothing     , Nothing      ) -> Nothing
      (Just _      , Nothing      ) -> error
        "Impossible happened. There is a max but the heap is empty."
      (Nothing     , Just _       ) -> error
        "Impossible happened. Heap is non-empty but there is a max."

  deleteMax :: heap -> Maybe heap
  deleteMax = fmap snd <$> decompose

--------------------------------------------------------------------------------
-- Inefficient list heap
--------------------------------------------------------------------------------

instance Ord a => Heap [ a ] where
  type Elem [ a ] = a

  isEmpty = null

  empty = []

  fromList xs = xs

  insert = (:)

  merge = (<>)

  decompose [] = Nothing
  decompose xs = Just (heapMax, left ++ tail right)
    where
    heapMax       = maximum xs
    (left, right) = span (/= heapMax) xs

--------------------------------------------------------------------------------
-- Unverified leftist heap
--------------------------------------------------------------------------------

data VanillaHeap a = Leaf | Node a Int (VanillaHeap a) (VanillaHeap a)

instance Ord a => Heap (VanillaHeap a) where
  type Elem (VanillaHeap a) = a

  isEmpty Leaf = True
  isEmpty _    = False

  empty = Leaf

  singleton x = Node x 0 Leaf Leaf

  merge Leaf heap = heap
  merge heap Leaf = heap
  merge h1@(Node x _ left1 right1)
        h2@(Node y _ left2 right2) =
    if x > y
      then mkNode x left1 (merge right1 h2)
      else mkNode y left2 (merge right2 h1)
    where
    mkNode :: a -> VanillaHeap a -> VanillaHeap a -> VanillaHeap a
    mkNode a heap1 heap2 =
      if rank heap1 <= rank heap2
        then Node a (rank heap1 + 1) heap2 heap1
        else Node a (rank heap2 + 1) heap1 heap2

    rank :: VanillaHeap a -> Int
    rank Leaf           = 0
    rank (Node _ r _ _) = r

  decompose Leaf                  = Nothing
  decompose (Node x _ left right) = Just (x, merge left right)

--------------------------------------------------------------------------------
-- Leftist heap with mechanised leftist invariant
--------------------------------------------------------------------------------

newtype Rank n = Rank { _unRank :: SNat n }

incRank :: Rank rank -> Rank ('S rank)
incRank (Rank snat) = Rank (SS snat)

data SafeHeap :: Nat -> Type -> Type where
  Leaf' :: SafeHeap 'Z a
  Node' :: a -> Rank ('S m)             -- Node' data
        -> SafeHeap n a -> SafeHeap m a -- Children
        -> m <= n                       -- Leftist invariant
        -> SafeHeap ('S m) a

data SafeHeapWrapped a = forall rank. SHW (SafeHeap rank a)

instance Ord a => Heap (SafeHeapWrapped a) where
  type Elem (SafeHeapWrapped a) = a

  isEmpty (SHW Leaf') = True
  isEmpty _        = False

  empty = SHW Leaf'

  singleton x = SHW $ Node' x (Rank (SS SZ)) Leaf' Leaf' Base

  merge (SHW Leaf') heap = heap
  merge heap (SHW Leaf') = heap
  merge heap1@(SHW (Node' x _ left1 right1 _))
        heap2@(SHW (Node' y _ left2 right2 _)) =
    if x > y
      then mkNode x (SHW left1) (merge (SHW right1) heap2)
      else mkNode y (SHW left2) (merge (SHW right2) heap1)
    where
    mkNode :: a -> SafeHeapWrapped a -> SafeHeapWrapped a -> SafeHeapWrapped a
    mkNode a (SHW h1) (SHW h2) =
      case lemAntiSym (_unRank . rank $ h1) (_unRank . rank $ h2) of
        Left  r1LEQr2 -> SHW $ Node' a (incRank $ rank h1) h2 h1 r1LEQr2
        Right r2LEQr1 -> SHW $ Node' a (incRank $ rank h2) h1 h2 r2LEQr1

    rank :: SafeHeap rank a -> Rank rank
    rank Leaf'             = Rank SZ
    rank (Node' _ r _ _ _) = r

  decompose (SHW safeHeap) =
    case safeHeap of
      Leaf'                  -> Nothing
      Node' x _ left right _ -> Just (x, merge (SHW left) (SHW right))

--------------------------------------------------------------------------------
-- Play it again Sam but this time with the heap invariant as well
--------------------------------------------------------------------------------

newtype Value n = Value { _unValue :: SNat n }

data SaferHeap :: Nat -> Nat -> Type where
  Leaf'' :: SaferHeap 'Z 'Z
  Node'' :: Value a -> Rank ('S m)         -- Node' data
         -> SaferHeap n b -> SaferHeap m c -- Children
         -> m <= n                         -- Leftist invariant
         -> b <= a -> c <= a               -- Heap invariant
         -> SaferHeap ('S m) a

data SaferHeapWrapped = forall rank value. SHW' (SaferHeap rank value)

data SaferHeapAlmostWrapped value = forall rank. SHAW (SaferHeap rank value)

instance Heap SaferHeapWrapped where
  type Elem SaferHeapWrapped = Nat

  isEmpty (SHW' Leaf'') = True
  isEmpty _             = False

  empty = SHW' Leaf''

  singleton x | SomeNat sX <- promote x = SHW' $
    Node'' (Value sX) (Rank (SS SZ))
           Leaf'' Leaf''
           Base
           (lemZLEQAll sX) (lemZLEQAll sX)

  merge (SHW' h1) (SHW' h2) | SHAW mergedHeap <- merge' (SHAW h1) (SHAW h2) =
    SHW' mergedHeap
    where
    merge' :: SaferHeapAlmostWrapped a -> SaferHeapAlmostWrapped b
           -> SaferHeapAlmostWrapped (Max a b)
    merge' (SHAW Leaf'') heap = heap
    merge' heap (SHAW Leaf'') = heap
    merge' (SHAW ha@(Node'' va@(Value sa) _ aLeft aRight _ lLEQa rLEQa))
           (SHAW hb@(Node'' vb@(Value sb) _ bLeft bRight _ lLEQb rLEQb)) =
      case lemAntiSym sa sb of
        Left  aLEQb | Refl <- lemMaxOfLEQ sa sb aLEQb ->
          let child1 = SHAW bLeft
              c1LEQp = lLEQb
              child2 = merge' (SHAW bRight) (SHAW ha)
              c2LEQp = lemDoubleLEQMax (unValue bRight) sa rLEQb aLEQb
          in mkNode vb child1 child2 c1LEQp c2LEQp
        Right bLEQa | Refl <- lemMaxSym sa sb
                    , Refl <- lemMaxOfLEQ sb sa bLEQa ->
          let child1 = SHAW aLeft
              c1LEQp = lLEQa
              child2 = merge' (SHAW aRight) (SHAW hb)
              c2LEQp = lemDoubleLEQMax (unValue aRight) sb rLEQa bLEQa
          in mkNode va child1 child2 c1LEQp c2LEQp

    mkNode :: Value c
           -> SaferHeapAlmostWrapped a -> SaferHeapAlmostWrapped b
           -> a <= c -> b <= c
           -> SaferHeapAlmostWrapped c
    mkNode vc (SHAW ha) (SHAW hb) aLEQc bLEQc =
      case lemAntiSym (_unRank . rank $ ha) (_unRank . rank $ hb) of
        Left  arLEQbr -> SHAW $ Node'' vc incARank hb ha arLEQbr bLEQc aLEQc
        Right brLEQar -> SHAW $ Node'' vc incBRank ha hb brLEQar aLEQc bLEQc
      where
      incARank = incRank $ rank ha
      incBRank = incRank $ rank hb

    rank :: SaferHeap rank val -> Rank rank
    rank Leaf''                 = Rank SZ
    rank (Node'' _ r _ _ _ _ _) = r

    value :: SaferHeap rank val -> Value val
    value Leaf''                   = Value SZ
    value (Node'' val _ _ _ _ _ _) = val

    unValue :: SaferHeap rank val -> SNat val
    unValue = _unValue . value

  decompose (SHW' saferHeap) =
    case saferHeap of
      Leaf''                      -> Nothing
      Node'' v _ left right _ _ _ ->
        Just (demote . _unValue $ v, merge (SHW' left) (SHW' right))

--------------------------------------------------------------------------------
-- Some theory building for <= and Max on natural numbers
--------------------------------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Show)

instance Ord Nat where
  Z     `compare` Z     = EQ
  Z     `compare` _     = LT
  _     `compare` Z     = GT
  (S n) `compare` (S m) = n `compare` m

data SNat :: Nat -> Type where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

data SomeNat = forall n. SomeNat (SNat n)

demote :: SNat n -> Nat
demote SZ     = Z
demote (SS n) = S (demote n)

promote :: Nat -> SomeNat
promote Z                                 = SomeNat SZ
promote (S n) | SomeNat snat <- promote n = SomeNat $ SS snat

data a :~: b where -- Same as Data.Type.Equality
  Refl :: a :~: a

data (<=) :: Nat -> Nat -> Type where
  Base   ::             'Z <= 'Z
  Single :: n <= m ->    n <= 'S m
  Double :: n <= m -> 'S n <= 'S m

lemZLEQAll :: SNat n -> 'Z <= n
lemZLEQAll SZ     = Base
lemZLEQAll (SS n) = Single (lemZLEQAll n)

lemAntiSym :: SNat n -> SNat m -> Either (n <= m) (m <= n)
lemAntiSym SZ m = Left  (lemZLEQAll m)
lemAntiSym n SZ = Right (lemZLEQAll n)
lemAntiSym (SS n) (SS m) =
  case lemAntiSym n m of
    Left  nLEQm -> Left  (Double nLEQm)
    Right mLEQn -> Right (Double mLEQn)

lemDecLEQ :: SNat n -> SNat m -> 'S n <= m -> n <= m
lemDecLEQ SZ      sm      _            = lemZLEQAll sm
lemDecLEQ _       SZ      _            = error "Impossible case."
lemDecLEQ sn      (SS sm) (Single leq) = Single (lemDecLEQ sn sm leq)
lemDecLEQ (SS sn) (SS sm) (Double leq) = Double (lemDecLEQ sn sm leq)

type family Max (n :: Nat) (m :: Nat) :: Nat where
  Max 'Z m          = m
  Max n 'Z          = n
  Max ('S n) ('S m) = 'S (Max n m)

lemMaxSym :: SNat x -> SNat y -> Max x y :~: Max y x
lemMaxSym SZ sy | Refl <- lemMaxOfLEQ SZ sy (lemZLEQAll sy) = Refl
lemMaxSym sx SZ | Refl <- lemMaxOfLEQ SZ sx (lemZLEQAll sx) = Refl
lemMaxSym (SS sx) (SS sy) | Refl <- lemMaxSym sx sy  = Refl

lemMaxOfLEQ :: SNat x -> SNat y -> x <= y -> Max x y :~: y
lemMaxOfLEQ SZ      _       _       = Refl
lemMaxOfLEQ (SS _)  SZ      _       = error "Impossible case."
lemMaxOfLEQ (SS sx) (SS sy) sxLEQsy =
  case sxLEQsy of
    Double xLEQy  | Refl <- lemMaxOfLEQ sx sy xLEQy                    -> Refl
    Single sxLEQy | Refl <- lemMaxOfLEQ sx sy (lemDecLEQ sx sy sxLEQy) -> Refl

lemMaxSelective :: SNat x -> SNat y -> Either (Max x y :~: x) (Max x y :~: y)
lemMaxSelective SZ _ = Right Refl
lemMaxSelective _ SZ = Left Refl
lemMaxSelective (SS sx) (SS sy) =
  case lemMaxSelective sx sy of
    Left  Refl -> Left  Refl
    Right Refl -> Right Refl

lemDoubleLEQMax :: SNat x -> SNat y -> x <= z -> y <= z -> Max x y <= z
lemDoubleLEQMax sx sy xLEQz yLEQz =
  case lemMaxSelective sx sy of
    Left  Refl -> xLEQz
    Right Refl -> yLEQz

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

data Action a = Insert a | DeleteMax deriving Show

instance Arbitrary Nat where
  arbitrary = fromInt . getPositive <$> arbitrary @(Positive Int)
    where
    fromInt 0 = Z
    fromInt n = S (fromInt (n - 1))

instance Arbitrary a => Arbitrary (Action a) where
  arbitrary = do
    n <- arbitrary @Int
    if n `mod` 2 == 0
      then Insert <$> arbitrary
      else pure DeleteMax

execAction :: Heap heap => Action (Elem heap) -> heap -> Maybe heap
execAction (Insert x) = Just . (x `insert`)
execAction DeleteMax  = deleteMax

carryOutActions :: Heap heap => [ Action (Elem heap) ] -> Maybe heap
carryOutActions = foldlM (flip execAction) empty

sameMaxAfterActions :: forall heap heap'
                     . Heap heap => Heap heap'
                    => Elem heap ~ Elem heap'
                    => Eq (Elem heap)
                    => [ Action (Elem heap) ] -> Bool
sameMaxAfterActions acts =
  (findMax <$> carryOutActions @heap  acts) ==
  (findMax <$> carryOutActions @heap' acts)

main :: IO ()
main = do
  quickCheck (sameMaxAfterActions @(VanillaHeap Int)     @[ Int ])
  quickCheck (sameMaxAfterActions @(SafeHeapWrapped Int) @[ Int ])
  quickCheck (sameMaxAfterActions @SaferHeapWrapped      @[ Nat ])

  putStrLn ""
  sampleActions <- sample' (arbitrary @(Action Int))
  print sampleActions
  print $ carryOutActions @[ Int ] sampleActions
