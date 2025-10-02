{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, TypeApplications,
ScopedTypeVariables, InstanceSigs, StandaloneDeriving, FlexibleContexts, UndecidableInstances, FlexibleInstances #-}
-- This file gather GADTs contain in stitch
-- stitch repo can be found in: https://gitlab.com/goldfirere/stitch/-/tree/hs2020 
import Data.Kind
import Language.Stitch.Data.Vec
import Language.Stitch.Data.Nat

-- SVec: https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Singletons.hs#L12-34
class SingKind k where
  -- It's a bit cleaner than the original approach to
  -- use a type family than a data family
  type Sing :: k -> Type

  -- | Convert a singleton to unrefined data
  fromSing :: forall (a :: k). Sing a -> k

  -- | Convert unrefined data to a singleton, in continuation-passing
  -- style.
  toSing :: k -> (forall (a :: k). Sing a -> r) -> r

-- implicit singletons
class SingI (a :: k) where
  sing :: Sing a

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Exp.hs#L52-96
data Exp :: forall n. Ctx n -> Ty -> Type where
  Var   :: Elem ctx ty -> Exp ctx ty
  Lam   :: STy arg -> Exp (arg :> ctx) res -> Exp ctx (arg :-> res)
  App   :: Exp ctx (arg :-> res) -> Exp ctx arg -> Exp ctx res
  Let   :: Exp ctx rhs_ty -> Exp (rhs_ty :> ctx) body_ty -> Exp ctx body_ty
  Arith :: Exp ctx TInt -> ArithOp ty -> Exp ctx TInt -> Exp ctx ty
  Cond  :: Exp ctx TBool -> Exp ctx ty -> Exp ctx ty -> Exp ctx ty
  Fix   :: Exp ctx (ty :-> ty) -> Exp ctx ty
  IntE  :: Int -> Exp ctx TInt
  BoolE :: Bool -> Exp ctx TBool

deriving instance Show (Exp ctx ty)

----------------------------------------------------
-- | Informative equality on expressions
eqExp :: Exp ctx ty1 -> Exp ctx ty2 -> Maybe (ty1 :~: ty2)
eqExp = go
  where
    go :: Exp ctx ty1 -> Exp ctx ty2 -> Maybe (ty1 :~: ty2)
    go (Var v1) (Var v2) = eqElem v1 v2
    go (Lam t1 b1) (Lam t2 b2) = do Refl <- testEquality t1 t2
                                    Refl <- go b1 b2
                                    return Refl
    go (App f1 a1) (App f2 a2) = do Refl <- go f1 f2
                                    Refl <- go a1 a2
                                    return Refl
    go (Let e1 b1) (Let e2 b2) = do Refl <- go e1 e2
                                    Refl <- go b1 b2
                                    return Refl
    go (Arith l1 op1 r1) (Arith l2 op2 r2) = do Refl <- go l1 l2
                                                Refl <- eqArithOp op1 op2
                                                Refl <- go r1 r2
                                                return Refl
    go (Cond c1 t1 f1) (Cond c2 t2 f2) = do Refl <- go c1 c2
                                            Refl <- go t1 t2
                                            Refl <- go f1 f2
                                            return Refl
    go (Fix b1) (Fix b2) = do Refl <- go b1 b2
                              return Refl
    go (IntE i1) (IntE i2) | i1 == i2  = Just Refl
                           | otherwise = Nothing
    go (BoolE b1) (BoolE b2) | b1 == b2  = Just Refl
                             | otherwise = Nothing

    go _ _ = Nothing


data SVec :: forall (a :: Type) (n :: Nat). Vec a n -> Type where
  SVNil :: SVec VNil
  (:%>) :: Sing a -> Sing as -> SVec (a :> as)
infixr 5 :%>

deriving instance ShowSingVec v => Show (SVec v)

instance SingKind a => SingKind (Vec a n) where
  type Sing = SVec

  fromSing SVNil     = VNil
  fromSing (h :%> t) = fromSing h :> fromSing t

  toSing VNil cont = cont SVNil
  toSing (h :> t) cont = toSing h $ \ sh ->
                         toSing t $ \ st ->
                         cont (sh :%> st)

instance SingI VNil where
  sing = SVNil
instance (SingI h, SingI t) => SingI (h :> t) where
  sing = sing :%> sing

-- | Make a Show constraint for a singleton vector
type family ShowSingVec (v :: Vec a n) :: Constraint where
  ShowSingVec VNil      = ()
  ShowSingVec (x :> xs) = (Show (Sing x), ShowSingVec xs)

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Exp.hs#L158-171
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

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Scratch.hs#L13-37

data FSnocVec :: forall a m. (forall n. Vec a (Succ n) -> Type) -> Vec a m -> Type where
  FNil :: forall (b :: forall n. Vec a (Succ n) -> Type). FSnocVec b VNil
  (:<:) :: forall (b :: forall n. Vec a (Succ n) -> Type) x xs. FSnocVec b xs -> b (x :> xs) -> FSnocVec b (x :> xs)
infixl 5 :<:

-- (Exp [] ty1, Exp [ty1] ty2, Exp [ty2:ty1] ty3, Exp [ty3:ty2:ty1] ty4, ..., Exp tys{n-1} tyn)

type family VTail (v :: Vec a (Succ n)) :: Vec a n where
  VTail (_ :> xs) = xs

type family VHead (v :: Vec a (Succ n)) :: a where
  VHead (x :> _) = x

newtype Exp' (tys :: Ctx (Succ n)) = Exp' (Exp (VTail tys) (VHead tys))

example :: FSnocVec Exp' ((Int -> Int) :> Bool :> Int :> VNil)
example = FNil :<: Exp' (IntE 5) :<: Exp' (BoolE False) :<: Exp' (Lam (typeRep @Int) (Var (ES (ES EZ))))

data Lets :: forall n. Ctx n -> Type where
  LNil :: Lets VNil
  (:<<:) :: Lets ctx -> Exp ctx ty -> Lets (ty :> ctx)
infixl 5 :<<:

ex2 :: Lets ((Int -> Int) :> Bool :> Int :> VNil)
ex2 = LNil :<<: IntE 5 :<<: BoolE False :<<: Lam (typeRep @Int) (Var (ES (ES EZ)))

-- Vec: https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Vec.hs#L12-15
data Vec :: Type -> Nat -> Type where
  VNil :: Vec a Zero
  (:>) :: a -> Vec a n -> Vec a (Succ n)
infixr 5 :>

--https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Vec.hs#L19-23
(!!!) :: Vec a n -> Fin n -> a
-- RAE: Oy. Need to reverse order b/c of laziness
vec !!! fin = case (fin, vec) of
  (FZ,   x :> _)  -> x
  (FS n, _ :> xs) -> xs !!! n

--https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/SNat.hs#L9-11
minus :: Sing n -> Fin n -> Nat
minus (SSucc n) (FS v) = n `minus` v
minus n         FZ     = fromSing n

-- Elem: https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Vec.hs#L59-61
data Elem :: forall a n. Vec a n -> a -> Type where
  EZ :: Elem (x :> xs) x
  ES :: Elem xs x -> Elem (y :> xs) x

--https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Vec.hs#L66-94 
eqElem :: Elem xs x1 -> Elem xs x2 -> Maybe (x1 :~: x2)
eqElem EZ EZ           = Just Refl
eqElem (ES e1) (ES e2) = eqElem e1 e2
eqElem _       _       = Nothing

instance TestEquality (Elem xs) where
  testEquality = eqElem

-- | Convert an 'Elem' to a proper de Bruijn index
elemToInt :: Elem ctx ty -> Int
elemToInt EZ     = 0
elemToInt (ES e) = 1 + elemToInt e

-- | Convert an 'Elem' to a 'Fin'
elemToFin :: Elem (ctx :: Vec a n) x -> Fin n
elemToFin EZ     = FZ
elemToFin (ES e) = FS (elemToFin e)

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

-- Fin: https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Fin.hs#L9-11
data Fin :: Nat -> Type where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

deriving instance Show (Fin n)

finToInt :: Fin n -> Int
finToInt FZ = 0
finToInt (FS n) = 1 + finToInt n

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Pretty.hs#L66-76
coloring :: Coloring
coloring = red :&: green :&: yellow :&: blue :&: magenta :&: cyan :&: coloring

applyColor :: forall n. SingI n => Fin n -> ApplyColor
applyColor v = go coloring (n `minus` v)
  where
    go (color :&: _) Zero      = color
    go (_ :&: rest)  (Succ n') = go rest n'

    n :: Sing n
    n = sing

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Pretty.hs#L84-85
-- | Print a variable
prettyVar :: forall n. SingI n => Fin n -> Doc
prettyVar v = applyColor v (char '#' <> int (finToInt v))

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Check.hs#L72-76
check_var :: Fin n -> Sing (ctx :: Ctx n)
                  -> (forall t. STy t -> Elem ctx t -> m r)
                  -> m r
check_var FZ     (ty :%> _)   k = k ty EZ
check_var (FS n) (_  :%> ctx) k = check_var n ctx $ \ty elem -> k ty (ES elem)


-- ArithOp: https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Op.hs#L43-45
data ArithOp ty where
  Plus, Minus, Times, Divide, Mod        :: ArithOp TInt
  Less, LessE, Greater, GreaterE, Equals :: ArithOp TBool


-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Op.hs#L47-101
-- | Extract the result type of an Op
arithType :: ArithOp ty -> STy ty
arithType Plus     = sing
arithType Minus    = sing
arithType Times    = sing
arithType Divide   = sing
arithType Mod      = sing
arithType Less     = sing
arithType LessE    = sing
arithType Greater  = sing
arithType GreaterE = sing
arithType Equals   = sing

-- | 'UArithOp' ("unchecked 'ArithOp'") is an existential package for
-- an 'ArithOp'
type UArithOp = SingEx ArithOp

-- | Build a 'UArithOp' using an implicit singleton
uArithOp :: SingI ty => ArithOp ty -> UArithOp
uArithOp = SingEx sing

-- | Convenient pattern synonym to hide the underlying representation of UArithOp
pattern UArithOp s op = SingEx s op
{-# COMPLETE UArithOp #-}

uPlus, uMinus, uTimes, uDivide, uMod, uLess, uLessE, uGreater,
  uGreaterE, uEquals :: UArithOp
uPlus     = uArithOp Plus
uMinus    = uArithOp Minus
uTimes    = uArithOp Times
uDivide   = uArithOp Divide
uMod      = uArithOp Mod
uLess     = uArithOp Less
uLessE    = uArithOp LessE
uGreater  = uArithOp Greater
uGreaterE = uArithOp GreaterE
uEquals   = uArithOp Equals

-- | Compare two 'ArithOp's (potentially of different types) for equality
eqArithOp :: ArithOp ty1 -> ArithOp ty2 -> Maybe (ty1 :~: ty2)
eqArithOp Plus     Plus     = Just Refl
eqArithOp Minus    Minus    = Just Refl
eqArithOp Times    Times    = Just Refl
eqArithOp Divide   Divide   = Just Refl
eqArithOp Mod      Mod      = Just Refl
eqArithOp Less     Less     = Just Refl
eqArithOp LessE    LessE    = Just Refl
eqArithOp Greater  Greater  = Just Refl
eqArithOp GreaterE GreaterE = Just Refl
eqArithOp Equals   Equals   = Just Refl
eqArithOp _        _        = Nothing

-- | Compare two 'ArithOp's for uninformative equality
eqArithOpB :: ArithOp ty1 -> ArithOp ty2 -> Bool
eqArithOpB op1 op2 = isJust (eqArithOp op1 op2)

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Exists.hs#L16-17
-- | Pack a type whose last index is to be existentially bound
data Ex :: (k -> Type) -> Type where
  Ex :: a i -> Ex a

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Exists.hs#L25-35
-- | Pack an existential
packEx :: a i -> Ex a
packEx = Ex

-- | Unpack an existential (CPS-style)
unpackEx :: Ex a -> (forall i. a i -> r) -> r
unpackEx (Ex x) k = k x

-- | Map a function over the packed existential
mapEx :: (forall i. a i -> b i) -> Ex a -> Ex b
mapEx f (Ex x) = Ex (f x)

-- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Exists.hs#L37-48
-- | Like 'Ex', but stores a singleton describing the
-- existentially bound index
data SingEx :: (k -> Type) -> Type where
  SingEx :: Sing i -> a i -> SingEx a

-- | Pack an existential with an explicit singleton
packSingEx :: Sing i -> a i -> SingEx a
packSingEx = SingEx

-- | Unpack an existential with an explicit singleton (CPS-style)
unpackSingEx :: SingEx a -> (forall i. Sing i -> a i -> r) -> r
unpackSingEx (SingEx s x) k = k s x

