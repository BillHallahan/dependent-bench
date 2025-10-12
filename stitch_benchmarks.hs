-- This file aims to find interesting benchmarks/functions from each gadt
-- Note for finding gadt in the corresponding file, we use the command: 
-- grep -R "data .* where" -n .

{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, TypeApplications,
ScopedTypeVariables, InstanceSigs, StandaloneDeriving, FlexibleContexts, UndecidableInstances, FlexibleInstances #-}
-- This file gather GADTs contain in stitch
-- stitch repo can be found in: https://gitlab.com/goldfirere/stitch/-/tree/hs2020 
import Data.Kind
import Language.Stitch.Data.Vec
import Language.Stitch.Data.Nat


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

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Eval.hs#L35-57 
-- | Substitute the first expression into the second. As a proposition,
-- this is the substitution lemma.
subst :: forall ctx s t.
         Exp ctx s -> Exp (s :> ctx) t -> Exp ctx t
subst e = go LZ
  where
    go :: Length (locals :: Ctx n) -> Exp (locals +++ s :> ctx) t0 -> Exp (locals +++ ctx) t0
    go len (Var v)          = subst_var len v
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    subst_var :: Length (locals :: Ctx n) -> Elem (locals +++ s :> ctx) t0
              -> Exp (locals +++ ctx) t0
    subst_var LZ       EZ     = e
    subst_var LZ       (ES v) = Var v
    subst_var (LS _)   EZ     = Var EZ
    subst_var (LS len) (ES v) = shift (subst_var len v)

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Eval.hs#L116-126
-- | Evaluate an expression, using big-step semantics.
eval :: Exp VNil t -> ValuePair t
eval (Var v)          = impossibleVar v
eval e@(Lam _ body)   = ValuePair e $ \ arg -> subst arg body
eval (App e1 e2)      = eval (apply (eval e1) (eval e2))
eval (Let e1 e2)      = eval (subst (expr $ eval e1) e2)
eval (Arith e1 op e2) = eval (arith (val $ eval e1) op (val $ eval e2))
eval (Cond e1 e2 e3)  = eval (cond (val $ eval e1) e2 e3)
eval (Fix e)          = eval (unfix (eval e))
eval e@(IntE n)       = ValuePair e n
eval e@(BoolE b)      = ValuePair e b

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Eval.hs#L134-159 
-- | Step an expression, either to another expression or to a value.
step :: Exp VNil ty -> StepResult ty
step (Var v)          = impossibleVar v
step e@(Lam _ body)   = Value (ValuePair e $ \ arg -> subst arg body)
step (App e1 e2)      = case step e1 of
                          Step e1'      -> Step (App e1' e2)
                          Value lam_val ->
                            case step e2 of
                              Step e2'      -> Step (App (expr lam_val) e2')
                              Value arg_val -> Step (apply lam_val arg_val)
step (Let e1 e2)      = case step e1 of
                          Step e1' -> Step (Let e1' e2)
                          Value e1 -> Step (subst (expr e1) e2)
step (Arith e1 op e2) = case step e1 of
                          Step e1' -> Step (Arith e1' op e2)
                          Value v1 -> case step e2 of
                            Step e2' -> Step (Arith (expr v1) op e2')
                            Value v2 -> Step (arith (val v1) op (val v2))
step (Cond e1 e2 e3)  = case step e1 of
                          Step e1' -> Step (Cond e1' e2 e3)
                          Value v1 -> Step (cond (val v1) e2 e3)
step (Fix e)          = case step e of
                          Step e' -> Step (Fix e')
                          Value v -> Step (unfix v)
step e@(IntE n)       = Value (ValuePair e n)
step e@(BoolE b)      = Value (ValuePair e b)

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

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Singletons.hs#L83-85
snatToInt :: SNat n -> Int
snatToInt SZero     = 0
snatToInt (SSucc n) = 1 + snatToInt n

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Fin.hs#L15-17
finToInt :: Fin n -> Int
finToInt FZ = 0
finToInt (FS n) = 1 + finToInt n

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L65-69
eqElem :: Elem xs x1 -> Elem xs x2 -> Maybe (x1 :~: x2)
eqElem EZ EZ           = Just Refl
eqElem (ES e1) (ES e2) = eqElem e1 e2
eqElem _       _       = Nothing

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L79-82
-- | Convert an 'Elem' to a 'Fin'
elemToFin :: Elem (ctx :: Vec a n) x -> Fin n
elemToFin EZ     = FZ
elemToFin (ES e) = FS (elemToFin e)

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L29-33
elemIndex :: Eq a => a -> Vec a n -> Maybe (Fin n)
elemIndex _ VNil = Nothing
elemIndex x (y :> ys)
  | x == y    = Just FZ
  | otherwise = FS <$> elemIndex x ys

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L84-94
-- | Weaken an 'Elem' to work against a larger vector.
weakenElem :: Length prefix -> Elem xs x -> Elem (prefix +++ xs) x
weakenElem LZ       e = e
weakenElem (LS len) e = ES (weakenElem len e)

-- | Strengthen an 'Elem' to work with a suffix of a vector. Fails when
-- the element in question ('x') occurs in the 'prefix'.
strengthenElem :: Length prefix -> Elem (prefix +++ xs) x -> Maybe (Elem xs x)
strengthenElem LZ       e      = Just e
strengthenElem (LS _)   EZ     = Nothing
strengthenElem (LS len) (ES e) = strengthenElem len e

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Exists.hs#L25-48
-- | Pack an existential
packEx :: a i -> Ex a
packEx = Ex

-- | Unpack an existential (CPS-style)
unpackEx :: Ex a -> (forall i. a i -> r) -> r
unpackEx (Ex x) k = k x

-- | Map a function over the packed existential
mapEx :: (forall i. a i -> b i) -> Ex a -> Ex b
mapEx f (Ex x) = Ex (f x)

-- | Pack an existential with an explicit singleton
packSingEx :: Sing i -> a i -> SingEx a
packSingEx = SingEx

-- | Unpack an existential with an explicit singleton (CPS-style)
unpackSingEx :: SingEx a -> (forall i. Sing i -> a i -> r) -> r
unpackSingEx (SingEx s x) k = k s x
