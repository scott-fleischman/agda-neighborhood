{-# OPTIONS --exact-split #-}

module RelationProof where

data 𝟘 : Set where
open import Agda.Builtin.Unit renaming (⊤ to 𝟙)

infixr 5 _×_ _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

Relation : Set → Set₁
Relation P = P → P → Set

Total : {P : Set}
  → (R : Relation P)
  → (Relation P)
Total R x y = R x y + R y x

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

_^_ : {P : Set}
  → (S T : Relation (Extend P))
  → (Relation (Extend P))
_^_ {P} S T lower upper = Σ P (λ p → S lower (value p) × T (value p) upper)

module Order
  (P : Set)
  (L : Relation P)
  (total : (x y : P) → Total L x y)
  where

  data BST (lower upper : Extend P) : Set where
    leaf : (lb : extend L lower upper) → BST lower upper
    node : (BST ^ BST) lower upper → BST lower upper

  insert : {lower upper : Extend P}
    → (extend L ^ extend L) lower upper
    → BST lower upper
    → BST lower upper
  insert (y , p1 , p2) (leaf lb) = node (y , leaf p1 , leaf p2)
  insert (y , p1 , p2) (node (p , left , right)) with total y p
  … | inl pp = node (p , insert (y , p1 , pp) left , right)
  … | inr pp = node (p , left , insert (y , pp , p2) right)

  rotR : {lower upper : Extend P} → BST lower upper → BST lower upper
  rotR (node (p , node (m , lt , mt) , rt))
     = node (m , lt , node (p , mt , rt))
  {-# CATCHALL #-}
  rotR t = t

module Test where
  open import Agda.Builtin.Nat using (Nat; zero; suc)

  data _≤_ : (x y : Nat) → Set where
    z≤ : (y : Nat) → zero ≤ y
    s≤s : {x y : Nat} → x ≤ y → suc x ≤ suc y

  total≤ : (x y : Nat) → Total _≤_ x y
  total≤ zero y = inl (z≤ y)
  total≤ (suc x) zero = inr (z≤ (suc x))
  total≤ (suc x) (suc y) with total≤ x y
  total≤ (suc x) (suc y) | inl p = inl (s≤s p)
  total≤ (suc x) (suc y) | inr p = inr (s≤s p)

  open Order Nat _≤_ total≤

  is-inl : {A B : Set} → A + B → Set
  is-inl (inl _) = 𝟙
  is-inl (inr _) = 𝟘

  _prove≤_ : (x y : Nat) → {p : is-inl (total≤ x y)} → x ≤ y
  _prove≤_ x y {p} with total≤ x y
  _prove≤_ x y | inl r = r
  _prove≤_ x y {} | inr _

  ex1 : BST ⊥ ⊤
  ex1 = leaf _

  ex2 : BST (value 9) (value 9)
  ex2 = node (9 , leaf (9 prove≤ 9) , leaf (9 prove≤ 9))

  ex3 : BST ⊥ ⊤
  ex3 = node (9 , node (8 , leaf _ , leaf (8 prove≤ 9)) , leaf _)

  ex4 : BST ⊥ ⊤
  ex4 = insert (9 , _ , _) (leaf _)

  ex5 : BST ⊥ ⊤
  ex5 = insert (9 , _ , _) (insert (6 , _ , _) (insert (12 , _ , _) (leaf _)))

  ex6 : BST ⊥ (value 100)
  ex6 = insert (9 , _ , (9 prove≤ 100)) (insert (6 , _ , (6 prove≤ 100)) (insert (12 , _ , (12 prove≤ 100)) (leaf _)))
