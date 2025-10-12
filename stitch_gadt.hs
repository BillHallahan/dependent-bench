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

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L12-15
data Vec :: Type -> Nat -> Type where
  VNil :: Vec a Zero
  (:>) :: a -> Vec a n -> Vec a (Succ n)
infixr 5 :>

-- https://gitlab.com/goldfirere/stitch/-/blob/main/src/Language/Stitch/Data/Vec.hs#L42-51
-- | @Length xs@ is a runtime witness for how long a vector @xs@ is.
-- @LZ :: Length xs@ says that @xs@ is empty.
-- @LS len :: Length xs@ tells you that @xs@ has one more element
-- than @len@ says.
-- A term of type @Length xs@ also serves as a proxy for @xs@.
data Length :: forall a n. Vec a n -> Type where
  LZ :: Length VNil
  LS :: Length xs -> Length (x :> xs)

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


