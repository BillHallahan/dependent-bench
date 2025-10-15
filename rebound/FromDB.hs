module FromDB where

import ReboundGadt

-- -- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Syntax/ScopedDeBruijn.hs#L45-L56
fromDB :: Term n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Term n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - (toInt i) -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b)(from n c)