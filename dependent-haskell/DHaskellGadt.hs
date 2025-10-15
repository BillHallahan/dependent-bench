{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module DHaskellGadt where 
-- This file aims to explore GADT in dependent-haskell
-- The corresponding paper can be found in https://dl.acm.org/doi/pdf/10.1145/2578854.2503786?casa_token=jYtk8m_Nxz8AAAAA:Iz-[…]aD0QBT2fUGHcjKA9pTqwy9izlO7F3PbmFzJ2gMF-e2J3uHvUWfOZfpRj3GqKwzw
-- dependent-haskell github: https://github.com/slindley/dependent-haskell/tree/master 

import Data.Monoid
import Control.Applicative
import Data.Foldable
import Data.Traversable

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L11C1-L25C1
data Nat = Z | S Nat

data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

class NATTY (n :: Nat) where
  natty :: Natty n

instance NATTY Z where
  natty = Zy

instance NATTY n => NATTY (S n) where
  natty = Sy natty

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L26-L29
-- natter effectively converts an explicit Natty to an implicit NATTY
-- natter :: Natty x -> (NATTY x => t) -> t
-- natter Zy     t = t
-- natter (Sy x) t = natter x t

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L31-L55
{- plus -}
type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance S m :+ n = S (m :+ n)

(/+/) :: Natty m -> Natty n -> Natty (m :+ n)
Zy /+/ n = n
Sy m /+/ n = Sy (m /+/ n)

{- minus -}
type family (m :: Nat) :- (n :: Nat) :: Nat
type instance Z   :- n   = Z
type instance S m :- Z   = S m
type instance S m :- S n = (m :- n)

(/-/) :: Natty m -> Natty n -> Natty (m :- n)
Zy   /-/ n    = Zy
Sy m /-/ Zy   = Sy m
Sy m /-/ Sy n = m /-/ n

{- max -}
type family Max (m :: Nat) (n :: Nat) :: Nat
type instance Max Z     n     = n
type instance Max (S m) Z     = S m
type instance Max (S m) (S n) = S (Max m n)

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L57-L60
-- maxn :: Natty m -> Natty n -> Natty (Max m n)
-- maxn Zy     n      = n
-- maxn (Sy m) Zy     = Sy m
-- maxn (Sy m) (Sy n) = Sy (maxn m n)

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L63-L66
data Cmp :: Nat -> Nat -> * where
  LTNat :: ((x :+ S z) ~ y,          Max x y ~ y, (x :- y) ~ Z)   => Natty z -> Cmp x y
  EQNat :: (x          ~ y,          Max x y ~ x, (x :- y) ~ Z)   =>            Cmp x y
  GTNat :: (x          ~ (y :+ S z), Max x y ~ x, (x :- y) ~ S z) => Natty z -> Cmp x y

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L68-L75
-- cmp :: Natty x -> Natty y -> Cmp x y
-- cmp Zy     Zy     = EQNat
-- cmp Zy     (Sy y) = LTNat y
-- cmp (Sy x) Zy     = GTNat x
-- cmp (Sy x) (Sy y) = case cmp x y of
--   LTNat z -> LTNat z
--   EQNat   -> EQNat
--   GTNat z -> GTNat z

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L77-L80
data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
  LTCuts :: Natty b -> CmpCuts a (S b :+ c) (a :+ S b) c
  EQCuts :: CmpCuts a b a b
  GTCuts :: Natty b -> CmpCuts (a :+ S b) c a (S b :+ c)

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L82-L89
-- cmpCuts :: ((a :+ b) ~ (c :+ d)) => Natty a -> Natty b -> Natty c -> Natty d -> CmpCuts a b c d
-- cmpCuts Zy b Zy     d  = EQCuts
-- cmpCuts Zy b (Sy c) d  = LTCuts c
-- cmpCuts (Sy a) b Zy d  = GTCuts a
-- cmpCuts (Sy a) b (Sy c) d = case cmpCuts a b c d of
--   LTCuts z -> LTCuts z
--   EQCuts   -> EQCuts
--   GTCuts z -> GTCuts z

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L101-L105
data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p xy -> Box p xy
  Clear :: Box p xy
  Hor :: Natty x1 -> Box p '(x1, y) -> Natty x2 -> Box p '(x2, y) -> Box p '(x1 :+ x2, y)
  Ver :: Natty y1 -> Box p '(x, y1) -> Natty y2 -> Box p '(x, y2) -> Box p '(x, y1 :+ y2)

type s :-> t = forall i. s i -> t i

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L109-L113
-- ebox :: (p :-> Box q) -> Box p :-> Box q
-- ebox f (Stuff b) = f b
-- ebox f Clear = Clear
-- ebox f (Hor x1 l x2 r) = Hor x1 (ebox f l) x2 (ebox f r)
-- ebox f (Ver y1 t y2 b) = Ver y1 (ebox f t) y2 (ebox f b)

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L148-L150
data Vec :: Nat -> * -> * where
  V0 :: Vec Z x
  (:>) :: x -> Vec n x -> Vec (S n) x

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L152-L154
-- vlength :: Vec n x -> Natty n
-- vlength V0        = Zy
-- vlength (x :> xs) = Sy (vlength xs)

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L159-L161
-- vcopies :: forall n x.Natty n -> x -> Vec n x
-- vcopies Zy x = V0
-- vcopies (Sy n) x = x :> vcopies n x   

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L163-L165
-- vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
-- vapp V0 V0 = V0
-- vapp (f :> fs) (s :> ss) = f s :> vapp fs ss

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/PlainCursor.hs#L27-L28
data WrappedNat :: * where
  WNat :: Natty n -> WrappedNat

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/PlainCursor.hs#L30-L33
-- wrapNat :: Int -> WrappedNat
-- wrapNat 0 = WNat Zy
-- wrapNat n = case wrapNat (n-1) of
--               WNat wn -> WNat (Sy wn)

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/PlainCursor.hs#L35-L37
-- intOfNat :: Natty n -> Int
-- intOfNat Zy = 0
-- intOfNat (Sy n) = 1 + intOfNat n