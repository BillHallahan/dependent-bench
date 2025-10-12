{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, TypeApplications,
ScopedTypeVariables, InstanceSigs, StandaloneDeriving, FlexibleContexts, UndecidableInstances, FlexibleInstances #-}
-- This file gather GADTs in stitch
-- stitch repo can be found in: https://gitlab.com/goldfirere/stitch/-/tree/hs2020 
import Data.Kind
import Language.Stitch.Data.Vec
import Language.Stitch.Data.Nat


-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Type.hs#L30-42
-- | The type of a Stitch expression
data Ty = TInt
        | TBool
        | Ty :-> Ty
  deriving (Show, Eq, Generic, Hashable)
infixr 0 :->

-- | The singleton for a Stitch type
data STy :: Ty -> Type where
  SInt   :: STy TInt
  SBool  :: STy TBool
  (::->) :: STy arg -> STy res -> STy (arg :-> res)
infixr 0 ::->

-- | A context is just a vector of types
type Ctx n = Vec Ty n

type KnownLength (ctx :: Ctx n) = SingI n

-- | @Exp ctx ty@ is a well-typed expression of type @ty@ in context
-- @ctx@. Note that a context is a list of types, where a type's index
-- in the list indicates the de Bruijn index of the associated term-level
-- variable.
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

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L42-51
-- | @Length xs@ is a runtime witness for how long a vector @xs@ is.
-- @LZ :: Length xs@ says that @xs@ is empty.
-- @LS len :: Length xs@ tells you that @xs@ has one more element
-- than @len@ says.
-- A term of type @Length xs@ also serves as a proxy for @xs@.
data Length :: forall a n. Vec a n -> Type where
  LZ :: Length VNil
  LS :: Length xs -> Length (x :> xs)

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L12-15
data Vec :: Type -> Nat -> Type where
  VNil :: Vec a Zero
  (:>) :: a -> Vec a n -> Vec a (Succ n)
infixr 5 :>

-- | Store a value in both expression form and value form.
-- The duplication avoids conversions later without losing the
-- tagless aspect of values. Note that the 'ValuePair' constructor
-- should not considered a value tag; this type could be inlined into
-- an unboxed tuple with the same semantics; the only loss would
-- be syntactic cleanliness.
data ValuePair :: Ty -> Type where
  ValuePair :: { expr :: Exp VNil ty
               , val  :: Value ty
               } -> ValuePair ty

-- | The result of stepping is either a reduction or the detection
-- of a value.
data StepResult :: Ty -> Type where
  Step  :: Exp VNil ty -> StepResult ty
  Value :: ValuePair ty -> StepResult ty

-- implicit singletons
class SingI (a :: k) where
  sing :: Sing a

instance Hashable (STy ty) where
  hashWithSalt s = hashWithSalt s . fromSing

instance SingKind Ty where
  type Sing = STy

  fromSing SInt       = TInt
  fromSing SBool      = TBool
  fromSing (a ::-> r) = fromSing a :-> fromSing r

  toSing TInt      cont = cont SInt
  toSing TBool     cont = cont SBool
  toSing (a :-> r) cont = toSing a $ \sa ->
                          toSing r $ \sr ->
                          cont (sa ::-> sr)

instance SingI TInt where
  sing = SInt
instance SingI TBool where
  sing = SBool
instance (SingI a, SingI r) => SingI (a :-> r) where
  sing = sing ::-> sing

-- | Informative equality on types
instance TestEquality STy where
  testEquality SInt SInt   = Just Refl
  testEquality SBool SBool = Just Refl
  testEquality (a1 ::-> r1) (a2 ::-> r2) = do
    Refl <- testEquality a1 a2
    Refl <- testEquality r1 r2
    return Refl
  testEquality _ _ = Nothing

-- | Extract the result type of an STy known to be an arrow
extractResType :: STy (arg :-> res) -> STy res
extractResType (_ ::-> res) = res


instance KnownLength ctx => Hashable (Exp ctx ty) where
  hashWithSalt s = go
    where
      go (Var e)          = hashDeBruijn s e sing
      go (Lam ty body)    = s `hashWithSalt` ty
                              `hashWithSalt` body
      go (App e1 e2)      = s `hashWithSalt` e1
                              `hashWithSalt` e2
      go (Let e1 e2)      = s `hashWithSalt` e1
                              `hashWithSalt` e2
      go (Arith e1 op e2) = s `hashWithSalt` e1
                              `hashWithSalt` op
                              `hashWithSalt` e2
      go (Cond c t f)     = s `hashWithSalt` c
                              `hashWithSalt` t
                              `hashWithSalt` f
      go (Fix body)       = s `hashWithSalt` body
      go (IntE n)         = s `hashWithSalt` n
      go (BoolE b)        = s `hashWithSalt` b

instance KnownLength ctx => IHashable (Exp ctx) where
  ihashWithSalt = hashWithSalt
  ihash = hash

instance KnownLength ctx => Hashable (Elem ctx ty) where
  hashWithSalt s v = hashDeBruijn s v sing

instance KnownLength ctx => IHashable (Elem ctx) where
  ihashWithSalt = hashWithSalt
  ihash = hash



-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/CSE.hs#L143-149
-- | A snoc-list (the "nil" is at the left) of expressions, where later elements
-- are in a deeper context than earlier ones.
data Lets :: forall n. (forall m. Ctx m -> Ty -> Type) -> Ctx n -> Type where
  LNil  :: forall (a :: forall m. Ctx m -> Ty -> Type). Lets a VNil
  (:<:) :: forall (a :: forall m. Ctx m -> Ty -> Type) ctx ty.
           Lets a ctx -> a ctx ty -> Lets a (ty :> ctx)
infixl 5 :<:

-- find in https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Singletons.hs#L31-34
data SVec :: forall (a :: Type) (n :: Nat). Vec a n -> Type where
  SVNil :: SVec VNil
  (:%>) :: Sing a -> Sing as -> SVec (a :> as)
infixr 5 :%>


-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Singletons.hs#L62-64
data SNat :: Nat -> Type where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

deriving instance Show (Length xs)

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L55-61
-- | @Elem xs x@ is evidence that @x@ is in the vector @xs@.
-- @EZ :: Elem xs x@ is evidence that @x@ is the first element of @xs@.
-- @ES ev :: Elem xs x@ is evidence that @x@ is one position later in
-- @xs@ than is indicated in @ev@
data Elem :: forall a n. Vec a n -> a -> Type where
  EZ :: Elem (x :> xs) x
  ES :: Elem xs x -> Elem (y :> xs) x

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Exists.hs#L15-23
-- | Pack a type whose last index is to be existentially bound
data Ex :: (k -> Type) -> Type where
  Ex :: a i -> Ex a

instance (forall i. Read (a i)) => Read (Ex a) where
  readsPrec prec s = fmap (first Ex) $ readsPrec prec s

instance (forall i. Show (a i)) => Show (Ex a) where
  show (Ex x) = show x

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Exists.hs#L37-40
-- | Like 'Ex', but stores a singleton describing the
-- existentially bound index
data SingEx :: (k -> Type) -> Type where
  SingEx :: Sing i -> a i -> SingEx a

data Vec :: Type -> Nat -> Type where
  VNil :: Vec a Zero
  (:>) :: a -> Vec a n -> Vec a (Succ n)
infixr 5 :>

deriving instance Show a => Show (Vec a n)

(!!!) :: Vec a n -> Fin n -> a
-- RAE: Oy. Need to reverse order b/c of laziness
vec !!! fin = case (fin, vec) of
  (FZ,   x :> _)  -> x
  (FS n, _ :> xs) -> xs !!! n

type family (v :: Vec a n) !!! (fin :: Fin n) :: a where
  (x :> _) !!!  FZ       = x
  (_ :> xs) !!! (FS fin) = xs !!! fin

type family (v1 :: Vec a n) +++ (v2 :: Vec a m) :: Vec a (n + m) where
  (_ :: Vec a Zero) +++ v2 = v2
  (x :> xs)         +++ v2 = x :> (xs +++ v2)
infixr 5 +++


-- | Pack a type whose last index is to be existentially bound
data Ex :: (k -> Type) -> Type where
  Ex :: a i -> Ex a

data Nat = Zero | Succ Nat
  deriving Show

data Fin :: Nat -> Type where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)
