{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module Vcopies where
import DHaskellGadt 


-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L159-L161
vcopies :: forall n x.Natty n -> x -> Vec n x
vcopies Zy x = V0
vcopies (Sy n) x = x :> vcopies n x   
