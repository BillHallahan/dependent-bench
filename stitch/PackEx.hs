{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}

module PackEx where
import StitchGadt
-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Exists.hs#L25-48
-- | Pack an existential
packEx :: a i -> Ex a
packEx = Ex
