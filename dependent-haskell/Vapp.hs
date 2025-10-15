{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module Vapp where
import DHaskellGadt 

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L163-L165
vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
vapp V0 V0 = V0
vapp (f :> fs) (s :> ss) = f s :> vapp fs ss