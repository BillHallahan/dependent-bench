{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}
module StrengthenElem where
import StitchGadt hiding (strengthenElem)

-- | Strengthen an 'Elem' to work with a suffix of a vector. Fails when
-- the element in question ('x') occurs in the 'prefix'.
strengthenElem :: Length prefix -> Elem (prefix +++ xs) x -> Maybe (Elem xs x)
strengthenElem LZ       e      = Just e
strengthenElem (LS _)   EZ     = Nothing
strengthenElem (LS len) (ES e) = strengthenElem len e