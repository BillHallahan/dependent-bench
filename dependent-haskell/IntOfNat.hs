{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module IntOfNat where
import DHaskellGadt 

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/PlainCursor.hs#L35-L37
intOfNat :: Natty n -> Int
intOfNat Zy = 0
intOfNat (Sy n) = 1 + intOfNat n