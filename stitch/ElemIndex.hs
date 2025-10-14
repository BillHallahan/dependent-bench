{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}


module ElemIndex where
import StitchGadt

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L29-33
elemIndex :: Eq a => a -> Vec a n -> Maybe (Fin n)
elemIndex _ VNil = Nothing
elemIndex x (y :> ys)
  | x == y    = Just FZ
  | otherwise = FS <$> elemIndex x ys
  