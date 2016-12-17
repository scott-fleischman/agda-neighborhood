{-# OPTIONS --exact-split #-}

module RelationProof where

data 𝟘 : Set where
open import Agda.Builtin.Unit renaming (⊤ to 𝟙)

Relation : Set → Set₁
Relation P = P → P → Set

data Total {P : Set} (R : Relation P) : (x y : P) → Set where
  xRy : {x y : P} → R x y → Total R x y
  yRx : {x y : P} → R y x → Total R x y

data Extend (A : Set) : Set where
  ⊤ : Extend A
  value : A → Extend A
  ⊥ : Extend A

extend : {A : Set}
  → (R : Relation A)
  → (Relation (Extend A))
extend R _ ⊤ = 𝟙
extend R ⊤ (value y) = 𝟘
extend R (value x) (value y) = R x y
extend R ⊥ (value y) = 𝟙
extend R _ ⊥ = 𝟘

record PivotedPair {P : Set} (S T : Relation (Extend P)) (lower upper : Extend P) : Set where
  constructor pivoted-pair
  field
    pivot : P
    fst : S lower (value pivot)
    snd : T (value pivot) upper

module Order
  (P : Set)
  (R : Relation P)
  (total : (x y : P) → Total R x y)
  where

  data BST (lower upper : Extend P) : Set where
    leaf : (r : extend R lower upper) → BST lower upper
    node : PivotedPair BST BST lower upper → BST lower upper

  insert : {lower upper : Extend P}
    → PivotedPair (extend R) (extend R) lower upper
    → BST lower upper
    → BST lower upper
  insert (pivoted-pair y pl pu) (leaf _) = node (pivoted-pair y (leaf pl) (leaf pu))
  insert (pivoted-pair y pl pu) (node (pivoted-pair p left right)) with total y p
  … | xRy yRp = node (pivoted-pair p (insert (pivoted-pair y pl yRp) left) right)
  … | yRx pRy = node (pivoted-pair p left (insert (pivoted-pair y pRy pu) right))

  rotR : {lower upper : Extend P} → BST lower upper → BST lower upper
  rotR (node (pivoted-pair p (node (pivoted-pair m lt mt)) rt))
     = node (pivoted-pair m lt (node (pivoted-pair p mt rt)))
  {-# CATCHALL #-}
  rotR t = t

module Test where
  open import Agda.Builtin.Nat using (Nat; zero; suc)

  data _≤_ : (x y : Nat) → Set where
    z≤ : (y : Nat) → zero ≤ y
    s≤s : {x y : Nat} → x ≤ y → suc x ≤ suc y

  total≤ : (x y : Nat) → Total _≤_ x y
  total≤ zero y = xRy (z≤ y)
  total≤ (suc x) zero = yRx (z≤ (suc x))
  total≤ (suc x) (suc y) with total≤ x y
  total≤ (suc x) (suc y) | xRy p = xRy (s≤s p)
  total≤ (suc x) (suc y) | yRx p = yRx (s≤s p)

  open Order Nat _≤_ total≤

  is-xRy : {P : Set} → {R : Relation P} → {x y : P} → Total R x y → Set
  is-xRy (xRy _) = 𝟙
  is-xRy (yRx _) = 𝟘

  _prove≤_ : (x y : Nat) → {p : is-xRy (total≤ x y)} → x ≤ y
  _prove≤_ x y {p} with total≤ x y
  _prove≤_ x y | xRy r = r
  _prove≤_ x y {} | yRx _

  ex1 : BST ⊥ ⊤
  ex1 = leaf _

  ex2 : BST (value 9) (value 9)
  ex2 = node (pivoted-pair 9 (leaf (9 prove≤ 9)) (leaf (9 prove≤ 9)))

  ex3 : BST ⊥ ⊤
  ex3 = node (pivoted-pair 9 (node (pivoted-pair 8 (leaf _) (leaf (8 prove≤ 9)))) (leaf _))

  ex4 : BST ⊥ ⊤
  ex4 = insert (pivoted-pair 9 _ _) (leaf _)

  ex5 : BST ⊥ ⊤
  ex5 = insert (pivoted-pair 9 _ _) (insert (pivoted-pair 6 _ _) (insert (pivoted-pair 12 _ _) (leaf _)))

  ex6 : BST ⊥ (value 100)
  ex6 = insert (pivoted-pair 9 _ (9 prove≤ 100)) (insert (pivoted-pair 6 _ (6 prove≤ 100)) (insert (pivoted-pair 12 _ (12 prove≤ 100)) (leaf _)))
