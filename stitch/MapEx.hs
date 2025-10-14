{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}

module MapEx where
import StitchGadt 

-- | Map a function over the packed existential
mapEx :: (forall i. a i -> b i) -> Ex a -> Ex b
mapEx f (Ex x) = Ex (f x)