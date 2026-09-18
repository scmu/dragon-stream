> import Data.Bits (xor)

=== Defining Gray Code ===

Let b0 be the stream of all natural numbers and b the stream of all
positive natural numbers.

> b0, b :: Stream Nat
> b0 = 0 : b
> b  = 1 : (2 * b) \/ (2 * b + 1)

E.g
  take 10 b = [1,2,3,4,5,6,7,8,9,10]

There is an function "xor" defined in Data.Bits, which works
for Int. We lift the function to streams:

> xors :: Stream Nat -> Stream Nat -> Stream Nat
> xors = zipWith xor

With that we can define the stream of gray code (starting with 1):

> g :: Stream Nat
> g = b `xors` (b0 \/ b)

Note that b0 \/ b = [0,1,1,2,2,3,3,4,4,5 ...] gives us b >> 1.

Indeed we have

   g = [1,3,2,6,7,5,4,12,13,15 ... ]

=== The Property to Prove ===

Define ft = [0,1,0,1...] and tf = [1,0,1,0...]

> zeros, ones, ft, tf :: Stream Nat
> zeros = 0 : zeros
> ones  = 1 : ones
> ft    = zeros \/ ones
> tf    = ones  \/ zeros

The aim now is to prove that

    g = 1 : (2 * g + tf) \/ (2 * g + ft)

That the equation above is a one-liner encoding the
same property you have proved:

   g 0      = 1
   g (2n)   = 2 * (g n) + εn
   g (1+2n) = 2 * (g n) + 1 - εn

since tf is the stream representing εn (starting from n=1),
and ft is 1-εn.

=== The Main Proof ===

The proof goes (writing both `xor` and `xors` as (⊕)):

    g
  =   { definition of g }
    b ⊕ (b0 \/ b)
  =   { definitions }
    (1 : 2b \/ (2 b + 1)) ⊕ ((0 : b) \/ b)
  =   { definition of (‌\/) and (⊕), 1 ⊕ 0 = 1 }
    1 : (2b \/ (2b+1)) ⊕ (b \/ b))
  =   { zip-\/ exchange }
    1 : (2b ⊕ b) \/ ((2b+1) ⊕ b)
  =   { see below (1) }
    1 : (2g + tf) \/ (2g + ft)

Regarding (1): we now need to show that

        2b ⊕ b = 2g + tf           ----- (1)
    (2b+1) ⊕ b = 2g + ft           ----- (2)

=== Proof of (1) ===

To prove (1) we reason:

     2g + tf
   =   { definition of g }
     2 * (b ⊕ (b0 \/ b)) + tf
   =   { map-zip exchange, map-\/ exchange }
     2b ⊕ (2b0 \/ 2b) + tf
   =   { see below }
     2b ⊕ ((2b0 \/ 2b) + tf)
   =   { (2b0 \/ 2b) + tf = b, see below }
     2b ⊕ b

The penultimate step says that (+ tf) and (2b ⊕) . (2*) exchange,
that is:
      (2b ⊕ 2 xs) + tf= 2b ⊕ (2 xs + tf)
It is true if for all natural numbers m n we have
      (2m ⊕ 2n) + 0 = 2m ⊕ (2n + 0)
      (2m ⊕ 2n) + 1 = 2m ⊕ (2n + 1)
This is true because (2m ⊕ 2 n) always has 0 as their least
significant bits, while (+1) touches only the least sig. bit.

Regarding the last step we want to show that

      (2b0 \/ 2b) + tf = b                --- (3)

The proof goes:

      (2b0 \/ 2b) + tf
    =   { definitions }
      ((0 : 2b) \/ 2b) + (1 : ft)
    =   { definition of \/ }
      (0 : 2b \/ 2b) + (1 : ft)
    =   { definition of zip }
      1 : (2b \/ 2b) + ft
    =   { definition of ft }
      1 : (2b \/ 2b) + (zeros \/ ones)
    =   { zip-\/ exchange }
      1 : 2b \/ (2b+1)
    =   { definition }
      b

=== Proof of (2) ===

Proof of (2) is only slightly trickier:

      2g + ft
    =   { definition of g }
      2 * (b ⊕ (b0 \/ b)) + ft
    =   { map-zip exchange, map-\/ exchange }
      (2b ⊕ (2b0 \/ 2b)) + ft
    =   { see below  }
      (2b + 1) ⊕ ((2b0 \/ 2b) + tf)
    =   { again, (2b0 \/ 2b) + tf = b}
      (2b+1) ⊕ b

The penultimate step is true because for all m n :: Nat,

      (2m ⊕ 2n) + 0 = (2m + 1) ⊕ (2n + 1)
      (2m ⊕ 2n) + 1 = (2m + 1) ⊕ (2n + 0)

The last step is (3).

   ----

Alternatively, we can try to prove a property

      2b   ⊕ xs = 2c + tf
  ==> 2b+1 ⊕ xs = 2c + ft

which takes us from (2) to (3).

=== V ===

> v = g - (0 : g)

Alternative formulation of v:
  v = 1 : (tail g - g)

Defining alternating 1 and -1:

> pn = 1 : -1 : pn
> np = -1 : 1 : np

The aim is to prove that

  v = pn \/ 2v

Alternatively,

  v = 1 : 2v \/ np

Proof:

  Note that, by definition of (\/), we also have

    g = 1 : (tf + 2g) \/ (ft + 2g)
      =   { definition of (\/) }
        (1 : ft + 2g) \/ (tf + 2g)
      =   { arithmetics }
        (tf + (0:2g)) \/ (tf + 2g)

 Meanwhile, we can cast 0:g into the form xs \/ ys
   0 : g = 0 : (tf + (0:2g)) \/ (tf + 2g)
         =   { definition of (\/) }
           (0 : tf + 2g) \/ (tf + (0:2g))
         =   { definition of tf, ft, and (+) }
           (ft + (0:2g)) \/ (tf + (0:2g))

Main proof:

  v = g - (0:g)
    =  { alt. defs of g above }
      ((tf + (0:2g)) \/ (tf + 2g)) - ((ft + (0:2g)) \/ (tf + (0:2g)))
    =  { zip-(\/) exchange }
      ((tf + (0:2g)) - ((ft +(0:2g))) \/ ((tf + 2g) -(tf + (0:2g)))
    =  { arithmetics }
      (tf - ft) \/ (2g - (0:2g))
    =  { tf - ft = pn, arithmetics }
      pn \/ 2 (g - (0 : g))
    =  { definition of v }
      pn \/ 2v

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
