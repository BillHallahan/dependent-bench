{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}
module EqExpB where 

import StitchGadt
-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Exp.hs#L139-154
-- | Equality on expressions, needed for testing.
eqExpB :: Exp ctx ty1 -> Exp ctx ty2 -> Bool
-- Cannot be defined in terms of eqExp because the contexts might be different
eqExpB (Var e1)        (Var e2)        = elemToInt e1 == elemToInt e2
eqExpB (Lam ty1 body1) (Lam ty2 body2) | Just Refl <- ty1 `testEquality` ty2
                                       = body1 `eqExpB` body2
                                       | otherwise
                                       = False
eqExpB (App e1a e1b)   (App e2a e2b)   = e1a `eqExpB` e2a && e1b `eqExpB` e2b
eqExpB (Arith e1a op1 e1b) (Arith e2a op2 e2b)
  = e1a `eqExpB` e2a && op1 `eqArithOpB` op2 && e1b `eqExpB` e2b
eqExpB (Cond e1a e1b e1c) (Cond e2a e2b e2c)
  = e1a `eqExpB` e2a && e1b `eqExpB` e2b && e1c `eqExpB` e2c
eqExpB (IntE i1)     (IntE i2)     = i1 == i2
eqExpB (BoolE b1)    (BoolE b2)    = b1 == b2
eqExpB _             _             = False

