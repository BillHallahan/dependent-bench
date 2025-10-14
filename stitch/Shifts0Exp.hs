{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}
module Shifts0Exp where
import StitchGadt

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Shift.hs#L91-110
-- | If an expression is closed, we actually have no work to do. Unfortunately,
-- we cannot convince GHC of this fact, and so we have to recur out to the leaves
-- to fix the types.
shifts0Exp :: forall prefix ty. Exp VNil ty -> Exp prefix ty
shifts0Exp = go LZ
  where
    go :: Length (locals :: Ctx n) -> Exp locals ty0 -> Exp (locals +++ prefix) ty0
    go len (Var v)          = Var (shifts0_var v len)
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    shifts0_var :: Elem locals ty0 -> Length (locals :: Ctx n) -> Elem (locals +++ prefix) ty0
    shifts0_var EZ     _        = EZ
    shifts0_var (ES v) (LS len) = ES (shifts0_var v len)