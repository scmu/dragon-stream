> import Data.Bits (xor)

=== Defining the Stream of Positive Naturals ===

Let |b| be the stream of all positive natural numbers.

> b :: Stream Nat
> b = 1 : (2 * b) \/ (2 * b + 1)

Indeed,

  2b     = [2,4,6,8,...]
  2b + 1 = [3,5,7,9,...],

so that

  1 : (2b \/ (2b+1)) = [1,2,3,4,5,...] = b.

For example,

  take 10 b = [1,2,3,4,5,6,7,8,9,10].

=== Defining Gray Code Using Only b ===

There is a function |xor| defined in |Data.Bits|, which works for
|Int|. We lift the function to streams:

> xors :: Stream Nat -> Stream Nat -> Stream Nat
> xors = zipWith xor

The stream

  b \/ b = [1,1,2,2,3,3,4,4,...]

repeats every positive natural number twice. Therefore,

  0 : (b \/ b) = [0,1,1,2,2,3,3,4,...]

is the stream containing |n div 2| alongside each |n| in |b|.
Thus the stream of Gray-code values, starting from |G(1)|, is

> g :: Stream Nat
> g = b `xors` (0 : (b \/ b))

This is exactly the pointwise definition

  G(n) = n xor (n div 2).

For example,

  g = [1,3,2,6,7,5,4,12,13,15,...].

=== The Property to Prove ===

Define

  ft = [0,1,0,1,...]
  tf = [1,0,1,0,...].

> zeros, ones, ft, tf :: Stream Nat
> zeros = 0 : zeros
> ones  = 1 : ones
> ft    = zeros \/ ones
> tf    = ones  \/ zeros

The aim is to prove that

  g = 1 : ((2 * g + tf) \/ (2 * g + ft)).

This stream equation is a one-line encoding of

  G(1)    = 1,
  G(2n)   = 2 * G(n) + epsilon(n),
  G(2n+1) = 2 * G(n) + 1 - epsilon(n),

where |epsilon(n)| is 1 when |n| is odd and 0 when |n| is even.
The stream |tf| represents |epsilon(n)| for |n = 1,2,3,...|, while
|ft| represents |1 - epsilon(n)|.

=== The Main Proof ===

In the calculation below, both scalar |xor| and stream |xors| are
written as (xor).

    g
  =   { definition of g }
    b xor (0 : (b \/ b))
  =   { interleave definition of b }
    (1 : (2b \/ (2b+1))) xor (0 : (b \/ b))
  =   { definition of zip, and 1 xor 0 = 1 }
    1 : ((2b \/ (2b+1)) xor (b \/ b))
  =   { zip-interleave exchange }
    1 : ((2b xor b) \/ ((2b+1) xor b))
  =   { Lemmas (1) and (2), proved below }
    1 : ((2g + tf) \/ (2g + ft)).

It remains to prove

      2b xor b = 2g + tf,                     -- (1)
  (2b+1) xor b = 2g + ft.                     -- (2)

=== A Common Stream Identity ===

Both proofs use the following identity:

  (0 : (2b \/ 2b)) + tf = b.                 -- (3)

The proof uses |tf = 1 : ft| and the zip-interleave exchange law:

    (0 : (2b \/ 2b)) + tf
  =   { tf = 1 : ft }
    (0 : (2b \/ 2b)) + (1 : ft)
  =   { definition of zip }
    1 : ((2b \/ 2b) + ft)
  =   { definition of ft }
    1 : ((2b \/ 2b) + (zeros \/ ones))
  =   { zip-interleave exchange }
    1 : ((2b + zeros) \/ (2b + ones))
  =   { definitions of zeros and ones }
    1 : (2b \/ (2b+1))
  =   { interleave definition of b }
    b.

Elementwise, the same identity says

  [0,2,2,4,4,6,6,...] + [1,0,1,0,1,0,1,...]
    = [1,2,3,4,5,6,7,...].

=== Proof of (1) ===

We calculate from the right-hand side:

    2g + tf
  =   { definition of g }
    2 * (b xor (0 : (b \/ b))) + tf
  =   { shifting both operands of xor one bit to the left }
    (2b xor (0 : (2b \/ 2b))) + tf
  =   { move the least-significant-bit stream inside xor }
    2b xor ((0 : (2b \/ 2b)) + tf)
  =   { identity (3) }
    2b xor b.

The penultimate step is valid pointwise because both operands of
|2m xor 2n| have least significant bit 0. For |e| equal to 0 or 1,

  (2m xor 2n) + e = 2m xor (2n + e).

Thus

  2b xor b = 2g + tf.

=== Proof of (2) ===

Again, we calculate from the right-hand side:

    2g + ft
  =   { definition of g and left-shift through xor }
    (2b xor (0 : (2b \/ 2b))) + ft
  =   { complementary least significant bits in ft and tf }
    (2b+1) xor ((0 : (2b \/ 2b)) + tf)
  =   { identity (3) }
    (2b+1) xor b.

The penultimate step follows from the two pointwise identities

  (2m xor 2n) + 0 = (2m+1) xor (2n+1),
  (2m xor 2n) + 1 = (2m+1) xor (2n+0).

At every position, the entries of |ft| and |tf| are complementary.
Thus

  (2b+1) xor b = 2g + ft.

Combining (1) and (2) with the main proof gives

  g = 1 : ((2g + tf) \/ (2g + ft)).

=== The Difference Stream v ===

Define the difference between consecutive Gray-code values:

> v :: Stream Int
> v = g - (0 : g)

Thus

  v = [G(1), G(2)-G(1), G(3)-G(2), ...]
    = [1,2,-1,4,1,-2,-1,8,...].

Define the two alternating streams

> pn, np :: Stream Int
> pn = 1 : -1 : pn
> np = -1 : 1 : np

The aim is to prove

  v = pn \/ 2v.

Equivalently, since |pn = 1 : np|,

  v = 1 : (2v \/ np).

First rewrite |g| in a form suitable for subtraction. From the
recursive equation for |g|,

    g
  = 1 : ((tf + 2g) \/ (ft + 2g))
  =   { definition of interleave }
    (1 : (ft + 2g)) \/ (tf + 2g)
  =   { tf = 1 : ft }
    (tf + (0 : 2g)) \/ (tf + 2g).             -- (4)

We also rewrite |0 : g|. Using (4),

    0 : g
  = 0 : ((tf + (0 : 2g)) \/ (tf + 2g))
  =   { definition of interleave }
    (0 : (tf + 2g)) \/ (tf + (0 : 2g))
  =   { 0 : tf = ft }
    (ft + (0 : 2g)) \/ (tf + (0 : 2g)).       -- (5)

Now subtract (5) from (4):

    v
  =   { definition of v }
    g - (0 : g)
  =   { equations (4) and (5) }
    ((tf + (0 : 2g)) \/ (tf + 2g))
      - ((ft + (0 : 2g)) \/ (tf + (0 : 2g)))
  =   { zip-interleave exchange }
    ((tf + (0 : 2g)) - (ft + (0 : 2g)))
      \/ ((tf + 2g) - (tf + (0 : 2g)))
  =   { stream arithmetic }
    (tf - ft) \/ (2g - (0 : 2g))
  =   { tf - ft = pn }
    pn \/ (2 * (g - (0 : g)))
  =   { definition of v }
    pn \/ 2v.

Therefore,

  v = pn \/ 2v.

=== Recovering the Dragon Sequence ===

The entries of |v| are not merely 1 and -1; their absolute values are
powers of two. The Dragon turn sequence is obtained from their signs:

> d :: Stream Int
> d = signum v

The equation |v = pn \/ 2v| also shows that no entry of |v| is zero.
Therefore |signum (2v) = signum v|, and

    d
  =   { definition of d }
    signum v
  =   { v = pn \/ 2v }
    signum (pn \/ 2v)
  =   { map-interleave exchange }
    signum pn \/ signum (2v)
  =   { entries of pn are already 1 or -1 }
    pn \/ signum v
  =   { definition of d }
    pn \/ d.

Thus the signs of consecutive Gray-code differences satisfy exactly
the interleave equation of the Dragon sequence:

  d = pn \/ d.

=== Definitions ===

> type List a = [a]
> type Stream a = [a]
> type Nat = Int
> type Bit = Int

> instance Num a => Num (Stream a) where
>  (+) = zipWith (+)
>  (*) = zipWith (*)
>  abs = map abs
>  signum = map signum
>  fromInteger x = repeat (fromInteger x)
>  negate = map negate

> (\/) :: Stream a -> Stream a -> Stream a
> (x:xs) \/ ys = x : (ys \/ xs)
