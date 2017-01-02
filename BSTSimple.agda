module BSTSimple where

data Extend (P : Set) : Set where
  top bottom : Extend P
  value : P -> Extend P

data ExtendRelation (P : Set) (R : P -> P -> Set) : (l u : Extend P) -> Set where
  any-rel-top : (l : Extend P) -> ExtendRelation P R l top
  bottom-rel-any : (u : Extend P) -> ExtendRelation P R bottom u
  relation : (l u : P) -> (r : R l u) -> ExtendRelation P R (value l) (value u)

data Total (P : Set) (R : P -> P -> Set) : (x y : P) -> Set where
  x-rel-y : (x y : P) -> (r : R x y) -> Total P R x y
  y-rel-x : (x y : P) -> (r : R x y) -> Total P R y x

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module BST
  (P : Set)
  (R : P -> P -> Set)
  (total : (x y : P) -> Total P R x y)
  where

  data BST (l u : Extend P) : Set where
    leaf : ExtendRelation P R l u -> BST l u
    node : (p : P) -> BST l (value p) -> BST (value p) u -> BST l u

  insert : (l u : Extend P)
    -> (np : P)
    -> ExtendRelation P R l (value np)
    -> ExtendRelation P R (value np) u
    -> BST l u
    -> BST l u
  insert l u np rl ru (leaf x) = node np (leaf rl) (leaf ru)
  insert l u np rl ru (node p lt rt) with total np p
  insert l u np rl ru (node p lt rt) | x-rel-y .np .p r = node p (insert l (value p) np rl (relation np p r) lt) rt
  insert l u np rl ru (node p lt rt) | y-rel-x .p .np r = node p lt (insert (value p) u np (relation p np r) ru rt)

module Test where
  data _<=_ : (n m : Nat) -> Set where
    zero<=any : (m : Nat) -> zero <= m
    suc<=suc : (n m : Nat) -> (r : n <= m) -> suc n <= suc m

  total : (n m : Nat) -> Total Nat _<=_ n m
  total zero m = x-rel-y zero m (zero<=any m)
  total (suc n) zero = y-rel-x zero (suc n) (zero<=any (suc n))
  total (suc n) (suc m) with total n m
  total (suc n) (suc m) | x-rel-y .n .m r = x-rel-y (suc n) (suc m) (suc<=suc n m r)
  total (suc n) (suc m) | y-rel-x .m .n r = y-rel-x (suc m) (suc n) (suc<=suc m n r)

  open BST Nat _<=_ total
  test1 : BST bottom top
  test1 = leaf (any-rel-top bottom)

  test2 : BST bottom top
  test2 = node 5 (leaf (bottom-rel-any (value 5))) (leaf (any-rel-top (value 5)))

  test2i : BST bottom top
  test2i = insert bottom top 5 (bottom-rel-any (value 5)) (any-rel-top (value 5)) (leaf (any-rel-top bottom))
