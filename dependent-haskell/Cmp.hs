{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module Cmp where
import DHaskellGadt 


-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L68-L75
cmp :: Natty x -> Natty y -> Cmp x y
cmp Zy     Zy     = EQNat
cmp Zy     (Sy y) = LTNat y
cmp (Sy x) Zy     = GTNat x
cmp (Sy x) (Sy y) = case cmp x y of
  LTNat z -> LTNat z
  EQNat   -> EQNat
  GTNat z -> GTNat z