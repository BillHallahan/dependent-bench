{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}

module ExprType where
import StitchGadt
import Data.Kind ( Type )

import Unsafe.Coerce
-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Exp.hs#L157-171
-- | Extract the type of an expression
exprType :: SVec ctx -> Exp ctx ty -> STy ty
exprType ctx (Var v) = go v ctx
  where
    go :: forall a n (v :: Vec a n) (x :: a). Elem v x -> SVec v -> Sing x
    go EZ     (h :%> _) = h
    go (ES e) (_ :%> t) = go e t
exprType ctx (Lam arg_ty body) = arg_ty ::-> exprType (arg_ty :%> ctx) body
exprType ctx (App fun _)       = extractResType $ exprType ctx fun
exprType ctx (Let e1 e2)       = exprType (exprType ctx e1 :%> ctx) e2
exprType _   (Arith _ op _)    = arithType op
exprType ctx (Cond _ e1 _)     = exprType ctx e1
exprType ctx (Fix body)        = extractResType $ exprType ctx body
exprType _   (IntE _)          = sing
exprType _   (BoolE _)         = sing
