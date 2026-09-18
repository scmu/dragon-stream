{-# LANGUAGE NPlusKPatterns #-}
module Dragon where

data Turn = L | R  deriving (Show, Eq)  -- left, right
type Nat = Int
type List a = [a]

inv :: Turn -> Turn
inv L = R
inv R = L

-- the "unfold" method

dragonU :: Nat -> List Turn
dragonU 0     = []
dragonU (n+1) = ts ++ [L] ++ map inv (reverse ts)
   where ts = dragonU n

-- the "interleave" method

dragonI :: Nat -> List Turn
dragonI 0     = []
dragonI (n+1) = interleave lr (dragonI n)

lr = L : R : lr
rl = R : L : rl

  -- This is not the usual "interleave":
  -- in interleave xs ys, it is assumed that xs is infinite,
  -- and when ys runs out the sequence ends with the head of xs.

interleave :: List a -> List a -> List a
interleave (x:xs) []     = [x]
interleave (x:xs) (y:ys) = x : y : interleave xs ys

-- Goal: prove that dragonU = dragon I.
--
-- Hint: dragonI = dragonU if they satisfy the same recursive equation.
-- That is,
--   dragonI (1+n) = dragonI n ++ [L] ++ map inv (reverse (dragonI n))

data Rot = C | A -- clockwise and anticlockwise

dragonU' :: List Rot -> List Turn
dragonU' []      = []
dragonU' (C:rs)  = ts ++ [L] ++ map inv (reverse ts) where ts = dragonU' rs
dragonU' (A:rs)  = ts ++ [R] ++ map inv (reverse ts) where ts = dragonU' rs

dragonI' :: List Rot -> List Turn
dragonI' = foldl opI []
  where ts `opI` C = lr `interleave` ts
        ts `opI` A = rl `interleave` ts
