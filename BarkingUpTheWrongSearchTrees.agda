module BarkingUpTheWrongSearchTrees where

data Zero : Set where
record One : Set where constructor it
data Two : Set where tt ff : Two

So : Two -> Set
So tt = One
So ff = Zero

not : Two -> Two
not tt = ff
not ff = tt

_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

if_then_else_ : forall {X} b
  -> So b => X
  -> So (not b) => X
  -> X
if tt then t else f = t
if ff then t else f = f
infix 1 if_then_else_

module BinarySearchTreeBad
  (P : Set)
  (le : P -> P -> Two)
  where

  data Tree : Set where
    leaf : Tree
    node : Tree -> P -> Tree -> Tree

  data STRange : Set where
    empty : STRange
    _-_ : (l u : P) -> STRange
  infix 9 _-_

  data Maybe (X : Set) : Set where
    yes : X -> Maybe X
    no : Maybe X

  _?>_ : forall {X} -> Two -> Maybe X -> Maybe X
  b ?> mx = if b then mx else no
  infixr 4 _?>_

  valid : Tree -> Maybe STRange
  valid leaf = yes empty
  valid (node lt p rt) with valid lt | valid rt
  valid (node lt p rt) | yes empty | yes empty = yes empty
  valid (node lt p rt) | yes empty | yes (l - u) = le p l ?> yes (p - l)
  valid (node lt p rt) | yes (l - u) | yes empty = le u p ?> yes (l - p)
  valid (node lt p rt) | yes (a - b) | yes (c - d) = le b p ?> le p c ?> yes (a - d)
  valid (node lt p rt) | yes x | no = no
  valid (node lt p rt) | no | y = no

  -- BST : STRange -> Set
  -- BST r ≅ { t : Tree | valid t = yes r }

  leftOK : STRange -> P -> Two
  leftOK empty y = tt
  leftOK (l - u) y = le u y

  rightOK : P -> STRange -> Two
  rightOK y empty = tt
  rightOK y (l - u) = le y l

  nodeRange : STRange -> P -> STRange -> STRange
  nodeRange empty p empty = p - p
  nodeRange empty p (l - u) = p - u
  nodeRange (l - u) p empty = l - p
  nodeRange (l - _) p (_ - u) = l - u

  data BST : STRange -> Set where
    leaf : BST empty
    node : forall {l r}
      -> BST l -> (p : P) -> BST r
      -> So (leftOK l p)
      => So (rightOK p r)
      => BST (nodeRange l p r)

  insertS : P -> Tree -> Tree
  insertS y leaf = node leaf y leaf
  insertS y (node lt p rt) =
    if le y p
    then node (insertS y lt) p rt
    else node lt p (insertS y rt)

  oRange : STRange -> P -> STRange
  oRange empty y = y - y
  oRange (l - u) y =
    if le y l then y - u
    else if le u y then l - y
    else l - u

  insert : forall {r} y -> BST r -> BST (oRange r y)
  insert y leaf = node leaf y leaf
  insert y (node lt p rt) =
    if le y p
    then node (insert y lt) p rt
    else node lt p (insert y rt)
