{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables,
             TypeFamilies, PolyKinds, TypeApplications,
             ViewPatterns, DataKinds,
             GADTs, LambdaCase, EmptyCase, StandaloneDeriving #-}
module InsertLets where
import StitchGadt
-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/CSE.hs#L81-134 
-- | Implements Step 1 from the general description of CSE, above
insertLets :: KnownLength ctx => Exp ctx ty -> Exp ctx ty
insertLets = fst . go
  where
    go :: forall ctx ty. KnownLength ctx => Exp ctx ty -> (Exp ctx ty, ExpSet ctx)
    go e@(Var {}) = (e, S.empty)
    go (Lam arg_ty e1)
      = let (e1', all_exprs) = go e1
            e' = Lam arg_ty e1' in
        mk_result e' [unshiftSet all_exprs]

    go (App e1 e2)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            e' = App e1' e2' in
        mk_result e' [all_exprs1, all_exprs2]

    go (Let e1 e2)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            e' = Let e1' e2'

            all_exprs2' = unshiftSet all_exprs2 in
        mk_result e' [all_exprs1, all_exprs2']

    go (Arith e1 op e2)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            e' = Arith e1' op e2' in
        mk_result e' [all_exprs1, all_exprs2]

    go (Cond e1 e2 e3)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            (e3', all_exprs3) = go e3
            e' = Cond e1' e2' e3' in
        mk_result e' [all_exprs1, all_exprs2, all_exprs3]

    go (Fix e1)
      = let (e1', all_exprs) = go e1
            e' = Fix e1' in
        mk_result e' [all_exprs]

    go e@(IntE {}) = (e, S.empty)
    go e@(BoolE {}) = (e, S.empty)

    mk_result :: KnownLength ctx => Exp ctx ty -> [ExpSet ctx] -> (Exp ctx ty, ExpSet ctx)
    mk_result e all_exprss
      = (mkLets common_exprs e, S.insert e all_exprs)
      where
        pairs = allPairs all_exprss
        inters = map (uncurry S.intersection) pairs
        common_exprs = S.toList (S.unions inters)
        all_exprs = S.unions all_exprss