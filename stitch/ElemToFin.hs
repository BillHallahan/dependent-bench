{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators,
             GADTs, TypeApplications,
             ScopedTypeVariables, InstanceSigs, StandaloneDeriving,
             FlexibleContexts, UndecidableInstances, FlexibleInstances,
             ViewPatterns, LambdaCase, EmptyCase #-}

module ElemToFin where
import StitchGadt hiding (elemToFin)

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L79-82
-- | Convert an 'Elem' to a 'Fin'
elemToFin :: Elem (ctx :: Vec a n) x -> Fin n
elemToFin EZ     = FZ
elemToFin (ES e) = FS (elemToFin e)