-- This file aims to explore Gadts in rebound 
-- rebound can be found in: https://github.com/sweirich/rebound
-- the corresponding paper can be found: https://arxiv.org/pdf/2509.13261
module ReboundGadt where
import Data.Kind


data Nat = Z | S Nat
  deriving (Eq, Show)

-- https://github.com/sweirich/rebound/blob/main/benchmark/lib/Util/IdInt.hs#L16-L18
newtype IdInt = IdInt Int
  deriving (Eq, Ord, Generic, Num)

-- It is handy to make IdInt enumerable.
instance Enum IdInt where
  toEnum i = IdInt i
  fromEnum (IdInt i) = i

data LC v = Var !v | Lam !v !(LC v) | App !(LC v) !(LC v) 
            | Bool !Bool | If !(LC v) !(LC v) !(LC v) deriving (Eq, Generic)

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Syntax/Lazy/ScopedDeBruijn.hs#L15-L20 
data Term :: Nat -> Type where
  DVar :: (Idx g) -> Term g
  DLam :: (Term ('S g)) -> Term g
  DApp :: (Term g) -> (Term g) -> Term g
  DBool :: Bool -> (Term g)
  DIf :: (Term g)-> (Term g) -> (Term g) -> Term g

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/IdInt.hs#L27-L29
-- 0 is the smallest identifier
firstBoundId :: IdInt
firstBoundId = toEnum 0

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Syntax/ScopedDeBruijn.hs#L45-L56
-- fromDB :: Term n -> LC IdInt
-- fromDB = from firstBoundId
--   where
--     from :: IdInt -> Term n -> LC IdInt
--     from (IdInt n) (DVar i)
--       | toInt i < 0 = Var (IdInt $ toInt i)
--       | toInt i >= n = Var (IdInt $ toInt i)
--       | otherwise = Var (IdInt (n - (toInt i) -1))
--     from n (DLam b) = Lam n (from (succ n) b)
--     from n (DApp f a) = App (from n f) (from n a)
--     from n (DBool b) = Bool b
--     from n (DIf a b c) = If (from n a) (from n b)(from n c)


-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Nat.hs#L14-L20
data Idx :: Nat -> Type where
  FZ :: Idx ('S n)
  FS :: Idx n -> Idx ('S n)

data SNat n where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)


type family Plus n m where
  Plus 'Z n = n
  Plus ('S m) n = 'S (Plus m n)

type family Pred (n :: Nat) :: Nat where
  Pred ('S n) = n

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Nat.hs#L31-L37
-- toInt :: Idx n -> Int
-- toInt FZ = 0
-- toInt (FS n) = 1 + toInt n

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Nat.hs#L35-L37
-- sNat2Int :: SNat n -> Int
-- sNat2Int SZ = 0
-- sNat2Int (SS n) = 1 + sNat2Int n

-- https://github.com/sweirich/rebound/blob/main/benchmark/lib/Support/Par/SubstScoped.hs#L38C1-L47C35
data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Inc :: !(SNat m) -> Sub a n (Plus m n) --  increment by m
  Cons :: (a m) -> !(Sub a n m) -> Sub a ('S n) m --  extend a substitution (like cons)
  (:<>) :: !(Sub a m n) -> !(Sub a n p) -> Sub a m p --  compose substitutions

infixr 9 :<> -- like usual composition  (.)

class SubstC (a :: Nat -> Type) where
  var :: Idx n -> a n
  subst :: Sub a n m -> a n -> a m

-- https://github.com/sweirich/rebound/blob/main/benchmark/lib/Support/Par/SubstScoped.hs#L49-L54
--  Value of the index x in the substitution s
-- applyS :: SubstC a => Sub a n m -> Idx n -> a m
-- applyS (Inc m) x = var (shift m x)
-- applyS (Cons ty _s) FZ = ty
-- applyS (Cons _ty s) (FS x) = applyS s x
-- applyS (s1 :<> s2) x = subst s2 (applyS s1 x)


