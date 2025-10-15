
module ToInt where

import ReboundGadt

-- https://github.com/sweirich/rebound/blob/5e71e7aaf2bd561b411138d48355f4e33284ebc6/benchmark/lib/Util/Nat.hs#L31-L37
toInt :: Idx n -> Int
toInt FZ = 0
toInt (FS n) = 1 + toInt n
