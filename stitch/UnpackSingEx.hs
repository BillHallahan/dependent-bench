{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}

module UnpackSingEx where
import StitchGadt 

-- | Unpack an existential with an explicit singleton (CPS-style)
unpackSingEx :: SingEx a -> (forall i. Sing i -> a i -> r) -> r
unpackSingEx (SingEx s x) k = k s x