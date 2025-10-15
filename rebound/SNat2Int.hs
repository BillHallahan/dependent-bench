

module SNat2Int where

import ReboundGadt

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Nat.hs#L35-L37
sNat2Int :: SNat n -> Int
sNat2Int SZ = 0
sNat2Int (SS n) = 1 + sNat2Int n