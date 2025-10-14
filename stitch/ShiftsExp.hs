{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}
module ShiftsExp where
import StitchGadt

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Shift.hs#L67-89
-- | Convert an expression typed in one context to one typed in a larger
-- context. Operationally, this amounts to de Bruijn index shifting.
-- As a proposition, this is the weakening lemma.
shiftsExp :: forall prefix ctx ty. Length prefix -> Exp ctx ty -> Exp (prefix +++ ctx) ty
shiftsExp prefix = go LZ
  where
    go :: Length (locals :: Ctx n) -> Exp (locals +++ ctx) ty0 -> Exp (locals +++ prefix +++ ctx) ty0
    go len (Var v)          = Var (shifts_var len v)
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    shifts_var :: Length (locals :: Ctx n)
               -> Elem (locals +++ ctx) ty0
               -> Elem (locals +++ prefix +++ ctx) ty0
    shifts_var LZ     v      = weakenElem prefix v
    shifts_var (LS _) EZ     = EZ
    shifts_var (LS l) (ES e) = ES (shifts_var l e)