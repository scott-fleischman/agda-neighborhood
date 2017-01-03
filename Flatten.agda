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

append : (l u : Bound)
  -> (p : Nat)
  -> OList l (lift p)
  -> OList (lift p) u
  -> OList l u
append l u p (nil l<=p) ys = {!!}
{-
Goal: OList l u
————————————————————————————————————————————————————————————
ys   : OList (lift p) u
l<=p : l <B= lift p
-}
append l u p (add x l<=x xs) ys = add x l<=x (append (lift x) u p xs ys)


-- try 2 (success but quadratic)

sandwich : (l u : Bound)
  -> (p : Nat)
  -> OList l (lift p)
  -> OList (lift p) u
  -> OList l u
sandwich l u p (nil pf) rl = add p pf rl
sandwich l u p (add x pf xs) ys = add x pf (sandwich (lift x) u p xs ys)

flatten : (l u : Bound) -> BST l u -> OList l u
flatten l u (leaf l<=u) = nil l<=u
flatten l u (node x lt rt) = sandwich l u x (flatten l (lift x) lt) (flatten (lift x) u rt)

flattenx : BSTx -> OListx
flattenx (bstx tree) = olistx (flatten bottom top tree)

fromList : List -> BSTx
fromList xs = foldr-list BSTx insertx xs (bstx (leaf unit))

sort : List -> OListx
sort xs = flattenx (fromList xs)

numbers : List
numbers = 86 :: 5 :: 57 :: 76 :: 73 :: 18 :: 42 :: 16 :: 22 :: 26 :: nil

-- Section 13

