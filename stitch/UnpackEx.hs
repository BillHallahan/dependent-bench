{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}
module UnpackEx where
import StitchGadt

-- | Unpack an existential (CPS-style)
unpackEx :: Ex a -> (forall i. a i -> r) -> r
unpackEx (Ex x) k = k x