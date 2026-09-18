> {-# OPTIONS_GHC -Wno-x-partial #-}

> type Bit = Int
> type Bits = List Bit

Known property of the positive and negative representations.
Since the name |n| is used a lot, we refer to the two representations
as |po| and |ne|.

po 0      = ne 0 = []
po (2n)   = po n ++ [0]
po (2n+1) = ne n ++ [1]
ne (2n)   = ne n ++ [0]
ne (2n-1) = po n ++ [-1]
  -- ne (2n+1) = po (n+1) ++ [-1]

> po :: Nat -> Bits
> po 0 = []
> po n | even n    = po (n `div` 2)     ++ [0]
>      | otherwise = ne ((n-1) `div` 2) ++ [1]

> ne :: Nat -> Bits
> ne 0 = []
> ne n | even n    = ne (n `div` 2)     ++ [0]
>      | otherwise = po ((n+1) `div` 2) ++ [-1]

=== Streams of Naturals ===

> toNat :: Bits -> Nat
> toNat [] = 0
> toNat xs = 2 * toNat (init xs) + last xs

> nats :: Stream Nat
> nats = 0 : 1 + nats

> b0, b :: Stream Nat
> b0 = 0 : b
> b  = 1 : (2 * b) \/ (2 * b + 1)

> ponats = map po (tail nats)
> nenats = map ne (tail nats)

> pos, nes :: Stream Bits
> pos = [1]    : map (++[0]) pos \/ map (++[ 1]) nes
> nes = [1,-1] : map (++[0]) nes \/ map (++[-1]) (tail pos)

> reps :: Stream (Nat, Bits, Bits)
> reps = zip3 (tail nats) pos nes

=== Choosing a Shorter Representation ===

Number of non-zero digits.

> nz :: Bits -> Int
> nz = length . filter (0 /=)

Which is shorter?

> m `sh` n | m < n = 1
>          | m > n = -1

Lifting |sh| to streams.

> shs :: Stream Int -> Stream Int -> Stream Int
> shs = zipWith sh

> ss = map nz pos `shs` map nz nes

Ideally we want to write both |sh| and |shs| as some infix
symbol.

=== ss is Dragon! ===

It turns out that

  ss = np \/ ss.

Abbreviating map nz to nz*, and write shs as ⧀.
Obvious properties:

  nz* pos = 1 : nz* pos \/ (nz* nes + 1)            -- (1)
  nz* nes = 2 : nz* nes \/ (nz* (tail pos) + 1)     -- (2)

equvalently,

  nz* pos = (1 : nz* nes + 1) \/ nz* pos            -- (1')
  nz* nes = (2 : nz* (tail pos) + 1) \/ nz* nes     -- (2')

Proof:

   ss
 =   {- definition -}
   nz* pos ⧀ nz* nes
 =   {- by (1') and (2') -}
   ((1 : nz* nes + 1) \/ nz* pos) ⧀
   ((2 : nz* (tail pos) + 1) \/ nz* nes)
 =   {- exchange law, definition of ss -}
   ((1 : nz* nes + 1) ⧀ (2 : nz* (tail pos) + 1)) \/ ss
 =   {- zip, definition of ⧀, |(xs+1) ⧀ (ys+1) = xs ⧀ ys|  -}
   (1 : nz* nes ⧀ nz* (tail pos)) \/ ss
 =   {- |nz* nes ⧀ nz* (tail pos) = np|, see below -}
   (1 : np) \/ ss
 =   {- 1 : np = pn  -}
   pn \/ ss

To prove that |nz* nes ⧀ nz* (tail pos) = np|

   nz* nes ⧀ nz* (tail pos)
 =   {- by (2') and (1) -}
   ((2 : nz* (tail pos) + 1) \/ nz* nes) ⧀
   (nz* pos \/ (nz* nes + 1) )
 =   {- exchange law -}
   ((2 : nz* (tail pos) + 1) ⧀ nz* pos) \/
   (nz* nes ⧀ (nz* nes + 1))
 =   {- |xs ⧀ (xs + 1) = (1 :: Stream Int)| -}
   ((2 : nz* (tail pos) + 1) ⧀ nz* pos) \/ 1
 =   {- |nz* pos = nz* (head pos) : nz* (tail pos) = 1 : nz* (tail pos)| -}
   ((2 : nz* (tail pos) + 1) ⧀ (1 : nz* (tail pos))) \/ 1
 =   {- zip, definition of ⧀ -}
   (-1 : (nz* (tail pos) + 1) ⧀ nz* (tail pos)) \/ 1
 =   {- (xs + 1) ⧀ xs = (-1 :: Steram Int) -}
   -1 \/ 1
 = np.


=== Definitions ===

> type List a = [a]
> type Stream a = [a]
> type Nat = Int


> instance Num a => Num (Stream a) where
>  (+) = zipWith (+)
>  (*) = zipWith (*)
>  abs = map abs
>  signum = map signum
>  fromInteger x = repeat (fromInteger x)
>  negate = map negate

> (\/) :: Stream a -> Stream a -> Stream a
> (x:xs) \/ ys = x : (ys \/ xs)

> pn, np :: Stream Int
> pn = 1 : -1 : pn
> np = -1 : 1 : np
