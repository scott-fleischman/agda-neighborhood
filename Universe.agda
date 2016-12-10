module Universe where

data 𝟘 : Set where
record 𝟙 : Set where
  constructor <>

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 5 _×_ _,_ _`×_
infixr 4 _+_ _`+_

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data JJ : Set where
  `R `P `1 : JJ
  _`+_ _`×_ : JJ → JJ → JJ

⟦_⟧ⱼⱼ : JJ → Set → Set → Set
⟦ `R ⟧ⱼⱼ R P = R
⟦ `P ⟧ⱼⱼ R P = P
⟦ `1 ⟧ⱼⱼ R P = 𝟙
⟦ S `+ T ⟧ⱼⱼ R P = ⟦ S ⟧ⱼⱼ R P + ⟦ T ⟧ⱼⱼ R P
⟦ S `× T ⟧ⱼⱼ R P = ⟦ S ⟧ⱼⱼ R P × ⟦ T ⟧ⱼⱼ R P

data μⱼⱼ (F : JJ) (P : Set) : Set where
  ⟨_⟩ : ⟦ F ⟧ⱼⱼ (μⱼⱼ F P) P → μⱼⱼ F P

record Applicative (H : Set → Set) : Set₁ where
  field
    pure : ∀ {X} → X → H X
    ap : ∀ {S T} → H (S → T) → H S → H T
open Applicative

traverse
  : ∀ {H F A B}
  → Applicative H
  → (A → H B)
  → μⱼⱼ F A
  → H (μⱼⱼ F B)
traverse {H} {F} {A} {B} AH h t = go `R t where
  pu = pure AH
  _⊛_ = ap AH
  infixl 5 _⊛_
  go : ∀ G
    → ⟦ G ⟧ⱼⱼ (μⱼⱼ F A) A
    → H (⟦ G ⟧ⱼⱼ (μⱼⱼ F B) B)
  go `R ⟨ t ⟩ = pu ⟨_⟩ ⊛ go F t
  go `P a = h a
  go `1 <> = pu <>
  go (S `+ T) (inl s) = pu inl ⊛ go S s
  go (S `+ T) (inr t) = pu inr ⊛ go T t
  go (S `× T) (s , t) = pu _,_ ⊛ go S s ⊛ go T t

id : {X : Set} → X → X
id x = x

idApp : Applicative (λ X → X)
idApp = record { pure = id; ap = id }

map : ∀ {F A B}
  → (A → B)
  → μⱼⱼ F A
  → μⱼⱼ F B
map = traverse idApp

record Monoid (X : Set) : Set where
  field
    neutral : X
    combine : X → X → X
  monApp : Applicative (λ _ → X)
  monApp = record { pure = λ _ → neutral ; ap = combine }
  crush : ∀ {P F} → (P → X) → μⱼⱼ F P → X
  crush = traverse {B = 𝟘} monApp
open Monoid

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

compMon : ∀ {X} → Monoid (X → X)
compMon = record { neutral = id ; combine = λ f g → f ∘ g }

foldr : ∀ {F A B}
  → (A → B → B)
  → B
  → μⱼⱼ F A
  → B
foldr f b t = crush compMon f t b

