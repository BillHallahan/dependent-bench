{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}
module PackSingEx where
import StitchGadt 
-- | Pack an existential with an explicit singleton
packSingEx :: Sing i -> a i -> SingEx a
packSingEx = SingEx