{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}

module ExpsToLets where
import StitchGadt

expsToLets :: [Ex (Exp ctx)]
           -> (forall n (prefix :: Ctx n). Lets (ShiftedExp ctx) prefix -> Length prefix -> r)
           -> r
expsToLets []              k = k LNil LZ
expsToLets (Ex exp : rest) k = expsToLets rest $ \ lets len ->
                               k (lets :<: ShiftedExp (shifts len exp)) (LS len)
                
-- | Wrap an expression in nested Lets. This version is efficient, shifting expressions
-- by many levels at once.
mkLets :: forall ctx ty. [Ex (Exp ctx)] -> Exp ctx ty -> Exp ctx ty
mkLets exps body = expsToLets exps $ \ lets len -> go lets (shifts len body)
  where
    go :: forall n (prefix :: Ctx n) ty.
          Lets (ShiftedExp ctx) prefix -> Exp (prefix +++ ctx) ty -> Exp ctx ty
    go LNil                      body = body
    go (rest :<: ShiftedExp exp) body = go rest (Let exp body)