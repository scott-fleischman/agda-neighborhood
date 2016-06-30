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

Total : {A : Set}
  → (R : A × A → Set)
  → (A × A → Set)
Total R (x , y) = R (x , y) + R (y , x)

data Extend (A : Set) : Set where
  ⊤ : Extend A
  value : A → Extend A
  ⊥ : Extend A

extend : {A : Set}
  → (R : A × A → Set)
  → (Extend A × Extend A → Set)
extend R (x , ⊤) = 𝟙
extend R (⊤ , value y) = 𝟘
extend R (value x , value y) = R (x , y)
extend R (⊥ , value y) = 𝟙
extend R (x , ⊥) = 𝟘

_^_ : {A : Set}
  → (S T : A × A → Set)
  → (A × A → Set)
_^_ {A} S T (lower , upper) = Σ A (λ p → S (lower , p) × T (p , upper))

module Order
  (P : Set)
  (L : P × P → Set)
  (total : (x y : P) → Total L (x , y))
  where

  data BST (b : Extend P × Extend P) : Set where
    leaf : (lb : extend L b) → BST b
    node : (BST ^ BST) b → BST b
