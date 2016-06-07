module Accept where

data 𝟘 : Set where
record 𝟙 : Set where
  constructor <>
data 𝟚 : Set where
  true false : 𝟚

So : 𝟚 → Set
So true = 𝟙
So false = 𝟘

¬ : 𝟚 → 𝟚
¬ true = false
¬ false = true

if_then_else_
  : {X : Set}
  → (b : 𝟚)
  → ({_ : So b} → X)
  → ({_ : So (¬ b)} → X)
  → X
if true then t else f = t
if false then t else f = f
infix 1 if_then_else_

magic : {X : Set} → 𝟘 → X
magic ()

example-value : 𝟚
example-value = if true then false else (λ {})

data Maybe (X : Set) : Set where
  yes : X → Maybe X
  no : Maybe X

_?>_ : ∀ {X} → 𝟚 → Maybe X → Maybe X
b ?> mx = if b then mx else no
infixr 4 _?>_

module Plain (P : Set) (_≤?_ : P → P → 𝟚) where
  data STRange : Set where
    ∅ : STRange
    _–_ : P → P → STRange
  infix 9 _–_

  data Tree : Set where
    leaf : Tree
    node : Tree → P → Tree → Tree

  valid : Tree → Maybe STRange
  valid leaf = yes ∅
  valid (node l x r) with valid l | valid r
  valid (node l x r) | yes ∅ | yes ∅ = yes (x – x)
  valid (node l x r) | yes ∅ | yes (rl – rh) = x ≤? rl ?> yes (x – rh)
  valid (node l x r) | yes (ll – lh) | yes ∅ = lh ≤? x ?> yes (ll – x)
  valid (node l x r) | yes (ll – lh) | yes (rl – rh) = lh ≤? x ?> x ≤? rl ?> yes (ll – rh)
  valid (node l x r) | _ | _ = no

  insert : P → Tree → Tree
  insert p leaf = node leaf p leaf
  insert p (node l x r) = if p ≤? x then node (insert p l) x r else node l x (insert p r)

module Search (P : Set) (_≤?_ : P → P → 𝟚) where
  data STRange : Set where
    ∅ : STRange
    _–_ : P → P → STRange
  infix 9 _–_

  leftOK : STRange → P → 𝟚
  leftOK ∅ p = true
  leftOK (low – high) p = high ≤? p

  rightOK : P → STRange → 𝟚
  rightOK p ∅ = true
  rightOK p (low – high) = p ≤? low

  outputRange : STRange → P → STRange → STRange
  outputRange ∅ p ∅ = p – p
  outputRange ∅ p (_ – hr) = p – hr
  outputRange (ll – _) p ∅ = ll – p
  outputRange (ll – _) _ (_ – hr) = ll – hr

  data BST : STRange → Set where
    leaf : BST ∅
    node
      : ∀ {left right}
      → BST left
      → (p : P)
      → BST right
      → {pl : So (leftOK left p)}
      → {pr : So (rightOK p right)}
      → BST (outputRange left p right)

  insertRange : STRange → P → STRange
  insertRange ∅ p = p – p
  insertRange (low – high) p =
    if p ≤? low then p – high
    else if high ≤? p then low – p
    else low – high

  insert : ∀ {r} y → BST r → BST (insertRange r y)
  insert y leaf = node leaf y leaf
  insert y (node left p right) =
    if y ≤? p then {!!} -- node (insert y left) p right
    else {!!} -- node left p (insert y right)
