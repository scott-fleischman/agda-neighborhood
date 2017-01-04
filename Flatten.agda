module Flatten where

data Zero : Set where
record One : Set where
  constructor unit

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Bound : Set where
  top bottom : Bound
  lift : Nat -> Bound

_<N=_ : (n m : Nat) -> Set
zero <N= y = One
suc x <N= zero = Zero
suc x <N= suc y = x <N= y

data _<N='_ : (n m : Nat) -> Set where
  zero<=any : (m : Nat) -> zero <N=' m
  suc<=suc : (n m : Nat) -> (r : n <N= m) -> suc n <N=' suc m

_<B=_ : (l u : Bound) -> Set
l <B= top = One
bottom <B= u = One
lift x <B= lift y = x <N= y
_ <B= _ = Zero

lift<= : (n m : Nat) -> (r : n <N= m) -> lift n <B= lift m
lift<= zero m r = unit
lift<= (suc n) zero ()
lift<= (suc n) (suc m) r = r

data _<B='_ : (l u : Bound) -> Set where
  any<=top : (l : Bound) -> l <B=' top
  lift : (n m : Nat) -> (r : n <N= m) -> lift n <B=' lift m
  bottom<=any : (u : Bound) -> bottom <B=' u

data Total : (n m : Nat) -> Set where
  total<N= : (n m : Nat) -> (r : n <N= m) -> Total n m
  total>N= : (n m : Nat) -> (r : m <N= n) -> Total n m

compare : (n m : Nat) -> Total n m
compare zero m = total<N= zero m unit
compare (suc n) zero = total>N= (suc n) zero unit
compare (suc n) (suc m) with compare n m
compare (suc n) (suc m) | total<N= .n .m r = total<N= (suc n) (suc m) r
compare (suc n) (suc m) | total>N= .n .m r = total>N= (suc n) (suc m) r

{-
compare : (n m : Nat) -> Total n m
compare zero m = total<N= zero m (zero<=any m)
compare (suc n) zero = total>N= (suc n) zero (zero<=any (suc n))
compare (suc n) (suc m) with compare n m
compare (suc n) (suc m) | total<N= .n .m r = total<N= (suc n) (suc m) (suc<=suc n m r)
compare (suc n) (suc m) | total>N= .n .m r = total>N= (suc n) (suc m) (suc<=suc m n r)
-}

data List : Set where
  nil : List
  _::_ : Nat -> List -> List
infixr 5 _::_

foldr-list : (A : Set) -> (Nat -> A -> A) -> List -> A -> A
foldr-list A f nil d = d
foldr-list A f (x :: xs) d = f x (foldr-list A f xs d)

data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (x : Nat)
    -> BST l (lift x)
    -> BST (lift x) u
    -> BST l u

insert : (l u : Bound)
  -> (x : Nat)
  -> l <B= lift x
  -> lift x <B= u
  -> BST l u
  -> BST l u
insert l u x lx xu (leaf lu) = node x (leaf lx) (leaf xu)
insert l u x lx xu (node p lt rt) with compare x p
insert l u x lx xu (node p lt rt) | total<N= .x .p r = node p (insert l (lift p) x lx (lift<= x p r) lt) rt
insert l u x lx xu (node p lt rt) | total>N= .x .p r = node p lt (insert (lift p) u x (lift<= p x r) xu rt)

data BSTx : Set where
  bstx : (tree : BST bottom top) -> BSTx

insertx : (n : Nat) -> BSTx -> BSTx
insertx n (bstx tree) = bstx (insert bottom top n unit unit tree)

data OList (l u : Bound) : Set where
  nil : l <B= u -> OList l u
  add : (x : Nat)
    -> l <B= lift x
    -> OList (lift x) u
    -> OList l u

data OListx : Set where
  olistx : (olist : OList bottom top) -> OListx

-- Section 12

-- try 1 (fail -- needs transitivity)

module Try1 where
  append : (l p u : Bound)
    -> OList l p
    -> OList p u
    -> OList l u
  append l u p (nil l<=p) ys = {!!}
  {-
  Goal: OList l p
  ————————————————————————————————————————————————————————————
  ys   : OList u p
  l<=p : l <B= u
  -}
  append l u p (add x l<=x xs) ys = add x l<=x (append (lift x) u p xs ys)


fromList : List -> BSTx
fromList xs = foldr-list BSTx insertx xs (bstx (leaf unit))

numbers : List
numbers = 91 :: 10 :: 73 :: 33 :: 61 :: 47 :: 78 :: 51 :: 86 :: 43 :: 30 :: 83 :: 16 :: 88 ::  1 :: 94 :: 69 ::  2 :: 72 :: 56 ::  9 :: 46 :: 58 ::  8 ::  4 :: 85 :: 21 :: 13 :: 18 :: 89 :: 55 :: 42 :: 62 :: 37 :: 45 :: 36 :: 100 :: 35 :: 96 :: 64 ::  5 :: 77 :: 31 ::  6 :: 26 :: 41 :: 24 :: 82 :: 22 :: 81 :: 84 :: 70 :: 44 :: 65 :: 75 :: 25 :: 28 :: 97 :: 79 :: 23 :: 53 :: 54 :: 19 :: 66 :: 99 ::  7 :: 48 :: 68 :: 98 :: 20 :: 76 :: 59 :: 90 ::  3 :: 95 :: 39 :: 63 :: 32 :: 74 :: 49 :: 11 :: 92 :: 17 :: 40 :: 29 :: 93 :: 67 :: 57 :: 27 :: 34 :: 12 :: 14 :: 87 :: 80 :: 71 :: 52 :: 15 :: 50 :: 60 :: 38 :: nil

-- try 2 (success but quadratic)

module Try2 where
  sandwich : (l u : Bound)
    -> (p : Nat)
    -> OList l (lift p)
    -> OList (lift p) u
    -> OList l u
  sandwich l u p (nil lp) ys = add p lp ys
  sandwich l u p (add x lx xs) ys = add x lx (sandwich (lift x) u p xs ys)

  flatten : (l u : Bound) -> BST l u -> OList l u
  flatten l u (leaf l<=u) = nil l<=u
  flatten l u (node x lt rt) = sandwich l u x (flatten l (lift x) lt) (flatten (lift x) u rt)

  flattenx : BSTx -> OListx
  flattenx (bstx tree) = olistx (flatten bottom top tree)

  sort : List -> OListx
  sort xs = flattenx (fromList xs)

-- Section 13

module Try3 where
  flapp : (l u : Bound)
    -> (p : Nat)
    -> BST l (lift p)
    -> OList (lift p) u
    -> OList l u
  flapp l u p (leaf lp) ys = add p lp ys
  flapp l u p (node p' tly typ) ys = flapp l u p' tly (flapp (lift p') u p typ ys)

  flatten : (l u : Bound)
    -> BST l u
    -> OList l u
  flatten l u (leaf lu) = nil lu
  flatten l u (node p lt rt) = flapp l u p lt (flatten (lift p) u rt)

  flattenx : BSTx -> OListx
  flattenx (bstx tree) = olistx (flatten bottom top tree)

  sort : List -> OListx
  sort xs = flattenx (fromList xs)


module Try4 where
  flapp : (l n u : Bound)
    -> BST l n
    -> ((m : Bound) -> m <B= n -> OList m u)
    -> OList l u
  flapp l n u (leaf ln) f = f l ln
  flapp l n u (node p lt rt) f = flapp l (lift p) u lt (λ m x → add p x (flapp (lift p) n u rt f))

  flatten : (l u : Bound)
    -> BST l u
    -> OList l u
  flatten l u t = flapp l u u t (λ m → nil)

  flattenx : BSTx -> OListx
  flattenx (bstx tree) = olistx (flatten bottom top tree)

  sort : List -> OListx
  sort xs = flattenx (fromList xs)
