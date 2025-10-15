{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}
module Natter where
import DHaskellGadt 
-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L26-L29
-- natter effectively converts an explicit Natty to an implicit NATTY
natter :: Natty x -> (NATTY x => t) -> t
natter Zy     t = t
natter (Sy x) t = natter x t