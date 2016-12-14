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

treeˢᵒ
  : ∀ {P F}
  → μˢᵒ F P
  → μˢᵒ `Tree P
treeˢᵒ {P} {F} ⟨ f ⟩ = go F f
  where
  go : ∀ G
    → ⟦ ⟦ G ⟧ˢᵒ ⟧ᴶᴶ (μˢᵒ F P) P
    → μˢᵒ `Tree P
  go `R x = treeˢᵒ x
  go `1 <> = ⟨ inl <> ⟩
  go (S `+ T) (inl s) = go S s
  go (S `+ T) (inr t) = go T t
  go (S `^ T) (s , p , t) = ⟨ inr (go S s , p , go T t) ⟩

data <⊥_⊤>ᵈ (P : Set) : Set where
  ⊤ : <⊥ P ⊤>ᵈ
  # : P → <⊥ P ⊤>ᵈ
  ⊥ : <⊥ P ⊤>ᵈ

Rel : Set → Set₁
Rel P = P × P → Set

<⊥_⊤>ᶠ : ∀ {P} → Rel P → Rel <⊥ P ⊤>ᵈ
<⊥ L ⊤>ᶠ (_ , ⊤) = 𝟙
<⊥ L ⊤>ᶠ (# x , # y) = L (x , y)
<⊥ L ⊤>ᶠ (⊥ , _) = 𝟙
<⊥ L ⊤>ᶠ (_ , _) = 𝟘

record ⌈_⌉ᵖ (P : Set) : Set where
  constructor !
  field {{proof}} : P

_⇒_ : Set → Set → Set
P ⇒ T = {{p : P}} → T
infixr 3 _⇒_

⌈_⌉ʳ : ∀ {P} → Rel P → Rel <⊥ P ⊤>ᵈ
⌈ L ⌉ʳ xy = ⌈ <⊥ L ⊤>ᶠ xy ⌉ᵖ

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

_˙^_ : ∀ {P} → (S T : Rel <⊥ P ⊤>ᵈ) → Rel <⊥ P ⊤>ᵈ
_˙^_ {P} S T (l , u) = Σ P λ p → S (l , # p) × T (# p , u)

pattern _‘_‘_ s p t = p , s , t
infixr 5 _‘_‘_

⟦_⟧≤ˢᵒ : SO → ∀ {P} → Rel <⊥ P ⊤>ᵈ → Rel P → Rel <⊥ P ⊤>ᵈ
⟦ `R ⟧≤ˢᵒ R L = R
⟦ `1 ⟧≤ˢᵒ R L = ⌈ L ⌉ʳ
⟦ S `+ T ⟧≤ˢᵒ R L = ⟦ S ⟧≤ˢᵒ R L ˙+ ⟦ T ⟧≤ˢᵒ R L
⟦ S `^ T ⟧≤ˢᵒ R L = ⟦ S ⟧≤ˢᵒ R L ˙^ ⟦ T ⟧≤ˢᵒ R L

data μ≤ˢᵒ (F : SO) {P : Set} (L : Rel P) (lu : <⊥ P ⊤>ᵈ × <⊥ P ⊤>ᵈ) : Set where
  ⟨_⟩ : ⟦ F ⟧≤ˢᵒ (μ≤ˢᵒ F L) L lu → μ≤ˢᵒ F L lu

_Δ : ∀ {P} → Rel P → Rel <⊥ P ⊤>ᵈ
L Δ = μ≤ˢᵒ `Tree L
pattern leaf = ⟨ inl ! ⟩
pattern node lp p pu = ⟨ inr (lp ‘ p ‘ pu) ⟩

_• : ∀ {P} → Rel P → Rel <⊥ P ⊤>ᵈ
L • = μ≤ˢᵒ `Interval L

pattern _° p = ⟨ (p , ! , !) ⟩

tree : ∀ {P F} {L : Rel P} → [ μ≤ˢᵒ F L ˙→ L Δ ]
tree {P} {F} {L} ⟨ f ⟩ = go F f where
  go : ∀ G → [ ⟦ G ⟧≤ˢᵒ (μ≤ˢᵒ F L) L ˙→ L Δ ]
  go `R x = tree x
  go `1 ! = leaf
  go (S `+ T) (inl s) = go S s
  go (S `+ T) (inr t) = go T t
  go (S `^ T) (s ‘ p ‘ t) = node (go S s) p (go T t)

OWOTO : ∀ {P} (L : Rel P) -> Rel P
OWOTO L (x , y) = ⌈ L (x , y) ⌉ᵖ + ⌈ L (y , x) ⌉ᵖ

module BSTGen {P : Set} (L : Rel P) (owoto : ∀ x y -> OWOTO L (x , y)) where

  insert : [ L • ˙→ L Δ ˙→ L Δ ]
  insert (y °) leaf = node leaf y leaf
  insert (y °) (node lt p rt) with owoto y p
  … | inl ! = node (insert (y °) lt) p rt
  … | inr ! = node lt p (insert (y °) rt)

  makeTree : ∀ {F} → μᴶᴶ F P → (L Δ) (⊥ , ⊤)
  makeTree = foldr (λ p → insert (p °)) leaf

_⁺ : ∀ {P} → Rel P → Rel <⊥ P ⊤>ᵈ
L ⁺ = μ≤ˢᵒ `List L

pattern [] = ⟨ inl ! ⟩
pattern _∷_ x xs = ⟨ inr (x , ! , xs) ⟩
infixr 6 _∷_

module Merger
  {P : Set}
  (L : Rel P)
  (owoto : ∀ x y -> OWOTO L (x , y))
  where
  merge : [ L ⁺ ˙→ L ⁺ ˙→ L ⁺ ]
  merge [] = id
  merge {l , u} (x ∷ xs) = go where
    go : ∀ {l} {{_ : <⊥ L ⊤>ᶠ (l , # x)}} → (L ⁺ ˙→ L ⁺) (l , u)
    go [] = x ∷ xs
    go (y ∷ ys) with owoto x y
    … | inl ! = x ∷ merge xs (y ∷ ys)
    … | inr ! = y ∷ go ys

  olMon : ∀ {lu} → <⊥ L ⊤>ᶠ lu ⇒ Monoid ((L ⁺) lu)
  olMon = record { neutral = [] ; combine = merge }

  mergeᴶᴶ : ∀ {F} → μᴶᴶ F P → (L ⁺) (⊥ , ⊤)
  mergeᴶᴶ = crush olMon (_∷ [])

  `qLTree : JJ
  `qLTree = (`1 `+ `P) `+ (`R `× `R)

  pattern none = ⟨ inl (inl <>) ⟩
  pattern one p = ⟨ inl (inr p) ⟩
  pattern fork l r = ⟨ inr (l , r) ⟩

  twistIn : P → μᴶᴶ `qLTree P → μᴶᴶ `qLTree P
  twistIn p none = one p
  twistIn p (one q) = fork (one p) (one q)
  twistIn p (fork l r) = fork (twistIn p r) l

  mergeSort : ∀ {F} → μᴶᴶ F P → (L ⁺) (⊥ , ⊤)
  mergeSort = mergeᴶᴶ ∘ foldr twistIn none

sandwich : ∀ {P} {L : Rel P} → [ (L ⁺) ˙^ (L ⁺) ˙→ (L ⁺) ]
sandwich ([] ‘ p ‘ ys) = p ∷ ys
sandwich (x ∷ xs ‘ p ‘ ys) = x ∷ sandwich (xs ‘ p ‘ ys)

flatten' : ∀ {P} {L : Rel P} → [ (L Δ) ˙→ (L ⁺) ]
flatten' leaf = []
flatten' (node l p r) = sandwich (flatten' l ‘ p ‘ flatten' r)

flatten≤ˢᵒ : ∀ {P} {L : Rel P} {F} → [ μ≤ˢᵒ F L ˙→ L ⁺ ]
flatten≤ˢᵒ = flatten' ∘ tree

infixr 8 _++_
RepL : ∀ {P} → Rel P → Rel <⊥ P ⊤>ᵈ
RepL L (n , u) = ∀ {m} → <⊥ L ⊤>ᶠ (m , n) ⇒ (L ⁺) (m , u)
_++_ : ∀ {P} {L : Rel P} {l n u}
  → (L ⁺) (l , n)
  → RepL L (n , u)
  → (L ⁺) (l , u)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

flapp : ∀ {P} {L : Rel P} {F} {l n u}
  → μ≤ˢᵒ F L (l , n)
  → RepL L (n , u)
  → (L ⁺) (l , u)
flapp {P} {L} {F} {u = u} t ys = go `R t ys
  where
  go : ∀ {l n} G
    → ⟦ G ⟧≤ˢᵒ (μ≤ˢᵒ F L) L (l , n)
    → RepL L (n , u)
    → (L ⁺) (l , u)
  go `R ⟨ t ⟩ ys = go F t ys
  go `1 ! ys = ys
  go (S `+ T) (inl s) ys = go S s ys
  go (S `+ T) (inr t) ys = go T t ys
  go (S `^ T) (s ‘ p ‘ t) ys = go S s (p ∷ go T t ys)

flatten : ∀ {P} {L : Rel P} {F} → [ μ≤ˢᵒ F L ˙→ (L ⁺) ]
flatten t = flapp t []
