module ApplyS where

import ReboundGadt

-- https://github.com/sweirich/rebound/blob/main/benchmark/lib/Support/Par/SubstScoped.hs#L49-L54
--  Value of the index x in the substitution s
applyS :: SubstC a => Sub a n m -> Idx n -> a m
applyS (Inc m) x = var (shift m x)
applyS (Cons ty _s) FZ = ty
applyS (Cons _ty s) (FS x) = applyS s x
applyS (s1 :<> s2) x = subst s2 (applyS s1 x)