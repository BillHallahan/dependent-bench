{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module Maxn where
import DHaskellGadt 

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L57-L60
maxn :: Natty m -> Natty n -> Natty (Max m n)
maxn Zy     n      = n
maxn (Sy m) Zy     = Sy m
maxn (Sy m) (Sy n) = Sy (maxn m n)