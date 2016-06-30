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

Relation : Set -> Set1
Relation P = P × P -> Set

Total : {P : Set}
  → (R : Relation P)
  → (Relation P)
Total R (x , y) = R (x , y) + R (y , x)

data Extend (A : Set) : Set where
  ⊤ : Extend A
  value : A → Extend A
  ⊥ : Extend A

extend : {A : Set}
  → (R : Relation A)
  → (Relation (Extend A))
extend R (x , ⊤) = 𝟙
extend R (⊤ , value y) = 𝟘
extend R (value x , value y) = R (x , y)
extend R (⊥ , value y) = 𝟙
extend R (x , ⊥) = 𝟘

_^_ : {P : Set}
  → (S T : Relation (Extend P))
  → (Relation (Extend P))
_^_ {P} S T (lower , upper) = Σ P (λ p → S (lower , value p) × T (value p , upper))

module Order
  (P : Set)
  (L : Relation P)
  (total : (x y : P) → Total L (x , y))
  where

  data BST (b : Extend P × Extend P) : Set where
    leaf : (lb : extend L b) → BST b
    node : (BST ^ BST) b → BST b

  insert : {b : Extend P × Extend P}
    → (extend L ^ extend L) b
    → BST b
    → BST b
  insert (y , p1 , p2) (leaf lb) = node (y , leaf p1 , leaf p2)
  insert (y , p1 , p2) (node (p , left , right)) with total y p
  insert (y , p1 , p2) (node (p , left , right)) | inl pp = node (p , insert (y , p1 , pp) left , right)
  insert (y , p1 , p2) (node (p , left , right)) | inr pp = node (p , left , insert (y , pp , p2) right)

  rotR : {b : Extend P × Extend P} → BST b → BST b
  rotR (node (p , node (m , lt , mt) , rt))
     = node (m , lt , node (p , mt , rt))
  {-# CATCHALL #-}
  rotR t = t
