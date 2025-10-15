{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}

module Vlength where
import DHaskellGadt 

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L152-L154
vlength :: Vec n x -> Natty n
vlength V0        = Zy
vlength (x :> xs) = Sy (vlength xs)