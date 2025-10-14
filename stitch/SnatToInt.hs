{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}

module SnatToInt where
import StitchGadt
-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Singletons.hs#L83-85
snatToInt :: SNat n -> Int
snatToInt SZero     = 0
snatToInt (SSucc n) = 1 + snatToInt n