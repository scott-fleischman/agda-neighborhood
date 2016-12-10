module Universe where

data 𝟘 : Set where
record 𝟙 : Set where
  constructor <>

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 5 _×_ _,_ _`×_ _˙×_
infixr 4 _+_ _`+_ _˙+_

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data JJ : Set where
  `R `P `1 : JJ
  _`+_ _`×_ : JJ → JJ → JJ

⟦_⟧ᴶᴶ : JJ → Set → Set → Set
⟦ `R ⟧ᴶᴶ R P = R
⟦ `P ⟧ᴶᴶ R P = P
⟦ `1 ⟧ᴶᴶ R P = 𝟙
⟦ S `+ T ⟧ᴶᴶ R P = ⟦ S ⟧ᴶᴶ R P + ⟦ T ⟧ᴶᴶ R P
⟦ S `× T ⟧ᴶᴶ R P = ⟦ S ⟧ᴶᴶ R P × ⟦ T ⟧ᴶᴶ R P

data μᴶᴶ (F : JJ) (P : Set) : Set where
  ⟨_⟩ : ⟦ F ⟧ᴶᴶ (μᴶᴶ F P) P → μᴶᴶ F P

record Applicative (H : Set → Set) : Set₁ where
  field
    pure : ∀ {X} → X → H X
    ap : ∀ {S T} → H (S → T) → H S → H T
open Applicative

traverse
  : ∀ {H F A B}
  → Applicative H
  → (A → H B)
  → μᴶᴶ F A
  → H (μᴶᴶ F B)
traverse {H} {F} {A} {B} AH h t = go `R t
  where
  pu = pure AH
  _⊛_ = ap AH
  infixl 5 _⊛_

  go : ∀ G
    → ⟦ G ⟧ᴶᴶ (μᴶᴶ F A) A
    → H (⟦ G ⟧ᴶᴶ (μᴶᴶ F B) B)
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
  → μᴶᴶ F A
  → μᴶᴶ F B
map = traverse idApp

record Monoid (X : Set) : Set where
  field
    neutral : X
    combine : X → X → X
  monApp : Applicative (λ _ → X)
  monApp = record { pure = λ _ → neutral ; ap = combine }
  crush : ∀ {P F} → (P → X) → μᴶᴶ F P → X
  crush = traverse {B = 𝟘} monApp
open Monoid

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

compMon : ∀ {X} → Monoid (X → X)
compMon = record { neutral = id ; combine = λ f g → f ∘ g }

foldr : ∀ {F A B}
  → (A → B → B)
  → B
  → μᴶᴶ F A
  → B
foldr f b t = crush compMon f t b


-- 10. The Simple Orderable Subuniverse of JJ

data SO : Set where
  `R `1 : SO
  _`+_ _`^_ : SO → SO → SO
infixr 5 _`^_

⟦_⟧ˢᵒ : SO → JJ
⟦ `R ⟧ˢᵒ = `R
⟦ `1 ⟧ˢᵒ = `1
⟦ S `+ T ⟧ˢᵒ = ⟦ S ⟧ˢᵒ `+ ⟦ T ⟧ˢᵒ
⟦ S `^ T ⟧ˢᵒ = ⟦ S ⟧ˢᵒ `× `P `× ⟦ T ⟧ˢᵒ

μˢᵒ : SO → Set → Set
μˢᵒ F P = μᴶᴶ ⟦ F ⟧ˢᵒ P

`List : SO
`List = `1 `+ (`1 `^ `R)
`Tree : SO
`Tree = `1 `+ (`R `^ `R)
`Interval : SO
`Interval = `1 `^ `1

tree
  : ∀ {P F}
  → μˢᵒ F P
  → μˢᵒ `Tree P
tree {P} {F} ⟨ f ⟩ = go F f
  where
  go : ∀ G
    → ⟦ ⟦ G ⟧ˢᵒ ⟧ᴶᴶ (μˢᵒ F P) P
    → μˢᵒ `Tree P
  go `R x = tree x
  go `1 <> = ⟨ inl <> ⟩
  go (S `+ T) (inl s) = go S s
  go (S `+ T) (inr t) = go T t
  go (S `^ T) (s , p , t) = ⟨ inr (go S s , p , go T t) ⟩

data <⊥_⊤> (P : Set) : Set where
  ⊤ : <⊥ P ⊤>
  # : P → <⊥ P ⊤>
  ⊥ : <⊥ P ⊤>

Rel : Set → Set₁
Rel P = P × P → Set

_⊥⊤ : ∀ {P} → Rel P → Rel <⊥ P ⊤>
(L ⊥⊤) (_ , ⊤) = 𝟙
(L ⊥⊤) (# x , # y) = L (x , y)
(L ⊥⊤) (⊥ , _) = 𝟙
(L ⊥⊤) (_ , _) = 𝟘


--⌈_⌉ : ∀ {P} → Rel P → Rel <⊥ P ⊤>
--⌈ L ⌉ xy = ⌈ ? ⌉

˙0 : {I : Set} → I → Set
˙0 i = 𝟘
˙1 : {I : Set} → I → Set
˙1 i = 𝟙

_˙+_ : {I : Set} → (f g : I → Set) → I → Set
(S ˙+ T) i = S i + T i
_˙×_ : {I : Set} → (f g : I → Set) → I → Set
(S ˙× T) i = S i × T i
_˙→_ : {I : Set} → (f g : I → Set) → I → Set
(S ˙→ T) i = S i → T i
infixr 2 _˙→_

[_] : {I : Set} → (I → Set) → Set
[ F ] = ∀ {i} → F i

⟦_⟧≤ˢᵒ : SO → ∀ {P} → Rel <⊥ P ⊤> → Rel P → Rel <⊥ P ⊤>
⟦ `R ⟧≤ˢᵒ R L = R
⟦ `1 ⟧≤ˢᵒ R L = {!!}
⟦ x `+ x₁ ⟧≤ˢᵒ R L = {!!}
⟦ x `^ x₁ ⟧≤ˢᵒ R L = {!!}
