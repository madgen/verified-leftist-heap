#!/usr/bin/env stack
-- stack script --resolver lts-14.6 --package QuickCheck --ghc-options -Wall

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

module VerifiedLeftistHeap
  ( main
  , Heap(..)
  , LeftistHeap, SafeHeap, SaferHeap
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

data LeftistHeap a = Leaf | Node a Int (LeftistHeap a) (LeftistHeap a)

class HasRank a where
  type RankType a
  rank :: a -> RankType a

instance HasRank (LeftistHeap a) where
  type RankType (LeftistHeap a) = Int

  rank Leaf           = 0
  rank (Node _ r _ _) = r

instance Ord a => Heap (LeftistHeap a) where
  type Elem (LeftistHeap a) = a

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
    mkNode :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
    mkNode a heap1 heap2 =
      if rank heap1 <= rank heap2
        then Node a (rank heap1 + 1) heap2 heap1
        else Node a (rank heap2 + 1) heap1 heap2

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

instance HasRank (SafeHeap rank val) where
  type RankType (SafeHeap rank val) = Rank rank

  rank Leaf'             = Rank SZ
  rank (Node' _ r _ _ _) = r

data SomeSafeHeap a = forall rank. SSH (SafeHeap rank a)

instance Ord a => Heap (SomeSafeHeap a) where
  type Elem (SomeSafeHeap a) = a

  isEmpty (SSH Leaf') = True
  isEmpty _        = False

  empty = SSH Leaf'

  singleton x = SSH singleton'
    where
    singleton' :: SafeHeap ('S 'Z) a
    singleton' = Node' x (Rank (SS SZ)) Leaf' Leaf' Base

  merge (SSH Leaf') heap = heap
  merge heap (SSH Leaf') = heap
  merge heap1@(SSH (Node' x _ left1 right1 _))
        heap2@(SSH (Node' y _ left2 right2 _)) =
    if x > y
      then mkNode x (SSH left1) (merge (SSH right1) heap2)
      else mkNode y (SSH left2) (merge (SSH right2) heap1)
    where
    mkNode :: a -> SomeSafeHeap a -> SomeSafeHeap a -> SomeSafeHeap a
    mkNode a (SSH h1) (SSH h2) =
      case lemAntiSym (_unRank . rank $ h1) (_unRank . rank $ h2) of
        Left  r1LEQr2 -> SSH $ Node' a (incRank $ rank h1) h2 h1 r1LEQr2
        Right r2LEQr1 -> SSH $ Node' a (incRank $ rank h2) h1 h2 r2LEQr1

  decompose (SSH safeHeap) =
    case safeHeap of
      Leaf'                  -> Nothing
      Node' x _ left right _ -> Just (x, merge (SSH left) (SSH right))

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

instance HasRank (SaferHeap rank val) where
  type RankType (SaferHeap rank val) = Rank rank

  rank Leaf''                 = Rank SZ
  rank (Node'' _ r _ _ _ _ _) = r

data SomeSaferHeap = forall rank value. SSH' (SaferHeap rank value)

data AlmostSomeSaferHeap value = forall rank. ASSH (SaferHeap rank value)

instance Heap SomeSaferHeap where
  type Elem SomeSaferHeap = Nat

  isEmpty (SSH' Leaf'') = True
  isEmpty _             = False

  empty = SSH' Leaf''

  singleton x | SomeNat sX <- promote x = SSH' $ singleton' sX
    where
    singleton' :: SNat val -> SaferHeap ('S 'Z) val
    singleton' sX = Node''
      (Value sX) (Rank (SS SZ))
      Leaf'' Leaf''
      Base
      (lemZLEQAll sX) (lemZLEQAll sX)

  merge (SSH' h1) (SSH' h2) | ASSH mergedHeap <- merge' (ASSH h1) (ASSH h2) =
    SSH' mergedHeap
    where
    merge' :: AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
           -> AlmostSomeSaferHeap (Max a b)
    merge' (ASSH Leaf'') heap = heap
    merge' heap (ASSH Leaf'') = heap
    merge' (ASSH ha@(Node'' va@(Value sa) _ aLeft aRight _ lLEQa rLEQa))
           (ASSH hb@(Node'' vb@(Value sb) _ bLeft bRight _ lLEQb rLEQb)) =
      case lemAntiSym sa sb of
        Left  aLEQb | Refl <- lemMaxOfLEQ aLEQb ->
          let child1 = ASSH bLeft
              c1LEQp = lLEQb
              child2 = merge' (ASSH bRight) (ASSH ha)
              c2LEQp = lemDoubleLEQMax rLEQb aLEQb
          in mkNode vb child1 child2 c1LEQp c2LEQp
        Right bLEQa | Refl <- lemMaxSym sa sb
                    , Refl <- lemMaxOfLEQ bLEQa ->
          let child1 = ASSH aLeft
              c1LEQp = lLEQa
              child2 = merge' (ASSH aRight) (ASSH hb)
              c2LEQp = lemDoubleLEQMax rLEQa bLEQa
          in mkNode va child1 child2 c1LEQp c2LEQp

    mkNode :: Value c
           -> AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
           -> a <= c -> b <= c
           -> AlmostSomeSaferHeap c
    mkNode vc (ASSH ha) (ASSH hb) aLEQc bLEQc =
      case lemAntiSym (_unRank . rank $ ha) (_unRank . rank $ hb) of
        Left  arLEQbr -> ASSH $ Node'' vc incARank hb ha arLEQbr bLEQc aLEQc
        Right brLEQar -> ASSH $ Node'' vc incBRank ha hb brLEQar aLEQc bLEQc
      where
      incARank = incRank $ rank ha
      incBRank = incRank $ rank hb

  decompose (SSH' saferHeap) =
    case saferHeap of
      Leaf''                      -> Nothing
      Node'' v _ left right _ _ _ ->
        Just (demote . _unValue $ v, merge (SSH' left) (SSH' right))

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

lemDecLEQ :: 'S n <= m -> n <= m
lemDecLEQ snLEQm =
  case recover snLEQm of
    (SS n, m) -> go n m snLEQm
  where
  go :: SNat n -> SNat m -> 'S n <= m -> n <= m
  go SZ     sm     _            = lemZLEQAll sm
  go _      SZ     _            = error "Impossible case."
  go _      (SS _) (Single leq) = Single (lemDecLEQ leq)
  go (SS _) (SS _) (Double leq) = Double (lemDecLEQ leq)

type family Max (n :: Nat) (m :: Nat) :: Nat where
  Max 'Z m          = m
  Max n 'Z          = n
  Max ('S n) ('S m) = 'S (Max n m)

lemMaxSym :: SNat x -> SNat y -> Max x y :~: Max y x
lemMaxSym SZ y          | Refl <- lemMaxOfLEQ $ lemZLEQAll y = Refl
lemMaxSym x SZ          | Refl <- lemMaxOfLEQ $ lemZLEQAll x = Refl
lemMaxSym (SS x) (SS y) | Refl <- lemMaxSym x y              = Refl

lemMaxOfLEQ :: x <= y -> Max x y :~: y
lemMaxOfLEQ Base                                        = Refl
lemMaxOfLEQ (Double xLEQy) | Refl  <- lemMaxOfLEQ xLEQy = Refl
lemMaxOfLEQ (Single xLEQy) | (x,_) <- recover     xLEQy =
  case x of
    SZ                                           -> Refl
    SS _ | Refl <- lemMaxOfLEQ (lemDecLEQ xLEQy) -> Refl

lemMaxSelective :: SNat x -> SNat y -> Either (Max x y :~: x) (Max x y :~: y)
lemMaxSelective SZ _ = Right Refl
lemMaxSelective _ SZ = Left Refl
lemMaxSelective (SS sx) (SS sy) =
  case lemMaxSelective sx sy of
    Left  Refl -> Left  Refl
    Right Refl -> Right Refl

lemDoubleLEQMax :: x <= z -> y <= z -> Max x y <= z
lemDoubleLEQMax xLEQz yLEQz =
  case lemMaxSelective (fst . recover $ xLEQz) (fst . recover $ yLEQz) of
    Left  Refl -> xLEQz
    Right Refl -> yLEQz

recover :: n <= m -> (SNat n, SNat m)
recover Base = (SZ, SZ)
recover (Single nLEQsm) | (n,m) <- recover nLEQsm = (   n, SS m)
recover (Double nLEQm)  | (n,m) <- recover nLEQm  = (SS n, SS m)

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
  quickCheck (sameMaxAfterActions @(LeftistHeap Int)  @[ Int ])
  quickCheck (sameMaxAfterActions @(SomeSafeHeap Int) @[ Int ])
  quickCheck (sameMaxAfterActions @SomeSaferHeap      @[ Nat ])

  putStrLn ""
  sampleActions <- sample' (arbitrary @(Action Int))
  print sampleActions
  print $ carryOutActions @[ Int ] sampleActions
