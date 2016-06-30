{-# OPTIONS --exact-split #-}

module RelationProof where

data 𝟘 : Set where
open import Agda.Builtin.Unit renaming (⊤ to 𝟙)

record Hide (P : Set) : Set where
  constructor hide
  field {{prf}} : P

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
Total R (x , y) = Hide (R (x , y)) + Hide (R (y , x))

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

hide-extend : {A : Set}
  → (R : Relation A)
  → (Relation (Extend A))
hide-extend L xy = Hide ((extend L) xy)

_^_ : {P : Set}
  → (S T : Relation (Extend P))
  → (Relation (Extend P))
_^_ {P} S T (lower , upper) = Σ P (λ p → S (lower , value p) × T (value p , upper))

extend^ : {P : Set} → (L : Relation P) -> (Relation (Extend P))
extend^ L = hide-extend L ^ hide-extend L

module Order
  (P : Set)
  (L : Relation P)
  (total : (x y : P) → Total L (x , y))
  where

  data BST (b : Extend P × Extend P) : Set where
    leaf : (lb : Hide (extend L b)) → BST b
    node : (BST ^ BST) b → BST b

  insert : {b : Extend P × Extend P}
    → extend^ L b
    → BST b
    → BST b
  insert (y , hide , hide) (leaf lb) = node (y , leaf hide , leaf hide)
  insert (y , hide , hide) (node (p , left , right)) with total y p
  insert (y , hide , hide) (node (p , left , right)) | inl hide = node (p , insert (y , hide , hide) left , right)
  insert (y , hide , hide) (node (p , left , right)) | inr hide = node (p , left , insert (y , hide , hide) right)
