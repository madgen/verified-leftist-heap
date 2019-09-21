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

  singleton x = Node x 1 Leaf Leaf

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
-- Leftist heap with mechanised leftist property
--------------------------------------------------------------------------------

newtype Rank n = Rank { _unRank :: SNat n }

inc :: Rank rank -> Rank ('S rank)
inc (Rank snat) = Rank (SS snat)

data SafeHeap :: Nat -> Type -> Type where
  Leaf' :: SafeHeap 'Z a
  Node' :: a -> Rank ('S m)             -- Node' data
        -> SafeHeap n a -> SafeHeap m a -- Children
        -> m <= n                       -- Leftist property
        -> SafeHeap ('S m) a

instance HasRank (SafeHeap rank label) where
  type RankType (SafeHeap rank label) = Rank rank

  rank Leaf'             = Rank SZ
  rank (Node' _ r _ _ _) = r

data SomeSafeHeap label = forall rank. SSH (SafeHeap rank label)

instance Ord label => Heap (SomeSafeHeap label) where
  type Elem (SomeSafeHeap label) = label

  isEmpty (SSH Leaf') = True
  isEmpty _        = False

  empty = SSH Leaf'

  singleton x = SSH singleton'
    where
    singleton' :: SafeHeap ('S 'Z) label
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
      case lemConnexity (_unRank . rank $ h1) (_unRank . rank $ h2) of
        Left  r1LEQr2 -> SSH $ Node' a (inc $ rank h1) h2 h1 r1LEQr2
        Right r2LEQr1 -> SSH $ Node' a (inc $ rank h2) h1 h2 r2LEQr1

  decompose (SSH safeHeap) =
    case safeHeap of
      Leaf'                  -> Nothing
      Node' x _ left right _ -> Just (x, merge (SSH left) (SSH right))

--------------------------------------------------------------------------------
-- Play it again Sam but this time with the heap property as well
--------------------------------------------------------------------------------

newtype Label n = Label { _unLabel :: SNat n }

data SaferHeap :: Nat -> Nat -> Type where
  Leaf'' :: SaferHeap 'Z 'Z
  Node'' :: Label a -> Rank ('S m)         -- Node'' data
         -> SaferHeap n b -> SaferHeap m c -- Children
         -> m <= n                         -- Leftist property
         -> b <= a -> c <= a               -- Heap property
         -> SaferHeap ('S m) a

instance HasRank (SaferHeap rank label) where
  type RankType (SaferHeap rank label) = Rank rank

  rank Leaf''                 = Rank SZ
  rank (Node'' _ r _ _ _ _ _) = r

data SomeSaferHeap = forall rank label. SSH' (SaferHeap rank label)

data AlmostSomeSaferHeap label = forall rank. ASSH (SaferHeap rank label)

instance Heap SomeSaferHeap where
  type Elem SomeSaferHeap = Nat

  isEmpty (SSH' Leaf'') = True
  isEmpty _             = False

  empty = SSH' Leaf''

  singleton x | SomeNat sX <- promote x = SSH' $ singleton' sX
    where
    singleton' :: SNat label -> SaferHeap ('S 'Z) label
    singleton' sX = Node''
      (Label sX) (Rank (SS SZ))
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
    merge' (ASSH hA@(Node'' vA@(Label sA) _ aLeft aRight _ lLEQa rLEQa))
           (ASSH hB@(Node'' vB@(Label sB) _ bLeft bRight _ lLEQb rLEQb)) =
      case lemConnexity sA sB of
        Left  aLEQb | Refl <- lemMaxOfLEQ aLEQb ->
          let child1 = ASSH bLeft
              c1LEQp = lLEQb
              child2 = merge' (ASSH bRight) (ASSH hA)
              c2LEQp = lemDoubleLEQMax rLEQb aLEQb
          in mkNode vB child1 child2 c1LEQp c2LEQp
        Right bLEQa | Refl <- lemMaxSym sA sB
                    , Refl <- lemMaxOfLEQ bLEQa ->
          let child1 = ASSH aLeft
              c1LEQp = lLEQa
              child2 = merge' (ASSH aRight) (ASSH hB)
              c2LEQp = lemDoubleLEQMax rLEQa bLEQa
          in mkNode vA child1 child2 c1LEQp c2LEQp

    mkNode :: Label c
           -> AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
           -> a <= c -> b <= c
           -> AlmostSomeSaferHeap c
    mkNode vc (ASSH hA) (ASSH hB) aLEQc bLEQc
      | rA <- rank hA, rB <- rank hB =
      case lemConnexity (_unRank rA) (_unRank rB) of
        Left  arLEQbr -> ASSH $ Node'' vc (inc rA) hB hA arLEQbr bLEQc aLEQc
        Right brLEQar -> ASSH $ Node'' vc (inc rB) hA hB brLEQar aLEQc bLEQc

  decompose (SSH' saferHeap) =
    case saferHeap of
      Leaf''                      -> Nothing
      Node'' v _ left right _ _ _ ->
        Just (demote . _unLabel $ v, merge (SSH' left) (SSH' right))

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

-- Doesn't type check!
--
-- promoteAttempt :: Nat -> SNat n
-- promoteAttempt Z                                = SZ
-- promoteAttempt (S n) | snat <- promoteAttempt n = SS snat

promote :: Nat -> SomeNat
promote Z                                 = SomeNat SZ
promote (S n) | SomeNat snat <- promote n = SomeNat $ SS snat

data (:~:) :: k -> k -> Type where -- Same as that in Data.Type.Equality
  Refl :: a :~: a

data (<=) :: Nat -> Nat -> Type where
  Base   ::             'Z <= 'Z
  Single :: n <= m ->    n <= 'S m
  Double :: n <= m -> 'S n <= 'S m

lemZLEQAll :: SNat n -> 'Z <= n
lemZLEQAll SZ     = Base
lemZLEQAll (SS x) = Single (lemZLEQAll x)

lemConnexity :: SNat n -> SNat m -> Either (n <= m) (m <= n)
lemConnexity SZ y = Left  (lemZLEQAll y)
lemConnexity x SZ = Right (lemZLEQAll x)
lemConnexity (SS x) (SS y) =
 case lemConnexity x y of
   Left  xLEQy -> Left  (Double xLEQy)
   Right yLEQx -> Right (Double yLEQx)

lemDecLEQ :: 'S n <= m -> n <= m
lemDecLEQ snLEQm =
  case recover snLEQm of
    (SS x, y) -> go x y snLEQm
  where
  go :: SNat n -> SNat m -> 'S n <= m -> n <= m
  go SZ     y      _            = lemZLEQAll y
  go _      SZ     _            = error "Impossible case."
  go _      (SS _) (Single leq) = Single (lemDecLEQ leq)
  go (SS _) (SS _) (Double leq) = Double (lemDecLEQ leq)

type family Max (n :: Nat) (m :: Nat) :: Nat where
  Max 'Z m          = m
  Max n 'Z          = n
  Max ('S n) ('S m) = 'S (Max n m)

lemMaxSym :: SNat n -> SNat m -> Max n m :~: Max m n
lemMaxSym SZ y          | Refl <- lemMaxOfLEQ $ lemZLEQAll y = Refl
lemMaxSym x SZ          | Refl <- lemMaxOfLEQ $ lemZLEQAll x = Refl
lemMaxSym (SS x) (SS y) | Refl <- lemMaxSym x y              = Refl

lemMaxOfLEQ :: n <= m -> Max n m :~: m
lemMaxOfLEQ Base                                        = Refl
lemMaxOfLEQ (Double xLEQy) | Refl  <- lemMaxOfLEQ xLEQy = Refl
lemMaxOfLEQ (Single xLEQy) | (x,_) <- recover     xLEQy =
  case x of
    SZ                                           -> Refl
    SS _ | Refl <- lemMaxOfLEQ (lemDecLEQ xLEQy) -> Refl

lemMaxSelective :: SNat n -> SNat m -> Either (Max n m :~: n) (Max n m :~: m)
lemMaxSelective SZ _ = Right Refl
lemMaxSelective _ SZ = Left Refl
lemMaxSelective (SS x) (SS y) =
  case lemMaxSelective x y of
    Left  Refl -> Left  Refl
    Right Refl -> Right Refl

lemDoubleLEQMax :: n <= l -> m <= l -> Max n m <= l
lemDoubleLEQMax nLEQl mLEQl =
  case lemMaxSelective (fst . recover $ nLEQl) (fst . recover $ mLEQl) of
    Left  Refl -> nLEQl
    Right Refl -> mLEQl

recover :: n <= m -> (SNat n, SNat m)
recover Base = (SZ, SZ)
recover (Single nLEQsm) | (x,y) <- recover nLEQsm = (   x, SS y)
recover (Double nLEQm)  | (x,y) <- recover nLEQm  = (SS x, SS y)

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
