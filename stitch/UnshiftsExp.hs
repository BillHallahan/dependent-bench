{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}
module UnshiftsExp where
import StitchGadt
import Data.Kind ( Type )

import Unsafe.Coerce

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Shift.hs#L116-142
-- | Unshift an expression. This is essentially a strengthening lemma, which fails
-- precisely when de Bruijn index of a free variable to be unshifted is too low.
unshiftsExp :: forall prefix ctx ty.
           Length prefix -> Exp (prefix +++ ctx) ty -> Maybe (Exp ctx ty)
unshiftsExp prefix = go LZ
  where
    go :: forall num_locals (locals :: Ctx num_locals) ty.
          Length locals
       -> Exp (locals +++ prefix +++ ctx) ty
       -> Maybe (Exp (locals +++ ctx) ty)
    go len (Var v)          = Var <$> unshift_var len v
    go len (Lam ty body)    = Lam ty <$> go (LS len) body
    go len (App e1 e2)      = App <$> go len e1 <*> go len e2
    go len (Let e1 e2)      = Let <$> go len e1 <*> go (LS len) e2
    go len (Arith e1 op e2) = Arith <$> go len e1 <*> pure op <*> go len e2
    go len (Cond e1 e2 e3)  = Cond <$> go len e1 <*> go len e2 <*> go len e3
    go len (Fix e)          = Fix <$> go len e
    go _   (IntE n)         = pure (IntE n)
    go _   (BoolE b)        = pure (BoolE b)

    unshift_var :: forall num_locals (locals :: Ctx num_locals) ty.
                   Length locals
                -> Elem (locals +++ prefix +++ ctx) ty
                -> Maybe (Elem (locals +++ ctx) ty)
    unshift_var LZ       v      = strengthenElem prefix v
    unshift_var (LS _)   EZ     = pure EZ
    unshift_var (LS len) (ES v) = ES <$> unshift_var len v