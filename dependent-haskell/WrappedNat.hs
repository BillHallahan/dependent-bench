{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module WrappedNat where
import DHaskellGadt 

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/PlainCursor.hs#L30-L33
wrapNat :: Int -> WrappedNat
wrapNat 0 = WNat Zy
wrapNat n = case wrapNat (n-1) of
              WNat wn -> WNat (Sy wn)