{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, FlexibleInstances #-}

module Ebox where
import DHaskellGadt 

-- https://github.com/slindley/dependent-haskell/blob/f0ea64b4e50464e8c60c11a82a7f432b0fccf122/OldBox/Box.hs#L109-L113
ebox :: (p :-> Box q) -> Box p :-> Box q
ebox f (Stuff b) = f b
ebox f Clear = Clear
ebox f (Hor x1 l x2 r) = Hor x1 (ebox f l) x2 (ebox f r)
ebox f (Ver y1 t y2 b) = Ver y1 (ebox f t) y2 (ebox f b)