module _ where

-- Prologomena

data Zero : Set where
record One : Set where
  constructor unit

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B
infixr 4 _+_

data _*_ (A B : Set) : Set where
  _/_ : A -> B -> A * B
infixr 5 _*_
infixr 5 _/_

id : {A : Set} -> A -> A
id x = x

_o_ : {A : Set}
  -> {B : A -> Set}
  -> {C : (a : A) -> B a -> Set}
  -> (f : {a : A} -> (b : B a) -> C a b)
  -> (g : (a : A) -> B a)
  -> (a : A)
  -> C a (g a)
(f o g) x = f (g x)


-- Universe

data JJ : Set where
  qR qP q1 : JJ
  _q+_ _q*_ : (S T : JJ) -> JJ
infixr 4 _q+_
infixr 5 _q*_

<!_!>JJ : JJ -> Set -> Set -> Set
<! qR !>JJ R P = R
<! qP !>JJ R P = P
<! q1 !>JJ R P = One
<! S q+ T !>JJ R P = <! S !>JJ R P + <! T !>JJ R P 
<! S q* T !>JJ R P = <! S !>JJ R P * <! T !>JJ R P

data MuJJ (F : JJ) (P : Set) : Set where
  la_ra : <! F !>JJ (MuJJ F P) P -> MuJJ F P


record Applicative (H : Set -> Set) : Set1 where
  field
    pure : {A : Set} -> A -> H A
    _<*>_ : {S T : Set} -> H (S -> T) -> H S -> H T
  infixl 5 _<*>_


traverse
  : {A B : Set}
  -> {F : JJ}
  -> {H : Set -> Set}
  -> Applicative H
  -> (A -> H B)
  -> MuJJ F A
  -> H (MuJJ F B)
traverse {A} {B} {F} {H} AH h t = go qR t
  where
  open Applicative AH
  go : (G : JJ)
    -> <! G !>JJ (MuJJ F A) A
    -> H (<! G !>JJ (MuJJ F B) B)
  go qR la t ra = pure la_ra <*> go F t
  go qP a = h a
  go q1 unit = pure unit
  go (S q+ T) (inl s) = pure inl <*> go S s
  go (S q+ T) (inr t) = pure inr <*> go T t
  go (S q* T) (s / t) = pure _/_ <*> go S s <*> go T t 

record Monoid (X : Set) : Set where
  field
    neutral : X
    combine : X -> X -> X
  monApp : Applicative (\ _ -> X)
  monApp = record { pure = \ _ -> neutral ; _<*>_ = combine }
  crush : {P : Set} -> {F : JJ} -> (P -> X) -> MuJJ F P -> X
  crush = traverse {B = Zero} monApp

compMon : {X : Set} -> Monoid (X -> X)
compMon = record { neutral = id ; combine = \ f g -> f o g }

foldr : {A B : Set}
  -> {F : JJ}
  -> (A -> B -> B)
  -> B
  -> MuJJ F A
  -> B
foldr f b t = Monoid.crush compMon f t b


-- Subuniverse

data SO : Set where
  qR q1 : SO
  _q+_ _q^_ : (S T : SO) -> SO

<!_!>SO : SO -> JJ
<! qR !>SO = qR
<! q1 !>SO = q1
<! S q+ T !>SO = <! S !>SO q+ <! T !>SO
<! S q^ T !>SO = <! S !>SO q* qP q* <! T !>SO

MuSO : SO -> Set -> Set
MuSO F P = MuJJ <! F !>SO P


qList : SO
qList = q1 q+ (q1 q^ qR)

qTree : SO
qTree = q1 q+ (qR q^ qR)

qInterval : SO
qInterval = q1 q^ q1

data Total {P : Set} (_<=_ : (x y : P) -> Set) : (x y : P) -> Set where
  x<=y : {x y : P} -> x <= y -> Total _<=_ x y
  y<=x : {x y : P} -> y <= x -> Total _<=_ x y

module Ordered
  (P : Set)
  (_<=_ : (x y : P) -> Set)
  (compare : (x y : P) -> Total _<=_ x y)
  where

  data Bound : Set where
    top bottom : Bound
    value : P -> Bound

  _<B=_ : ((x y : Bound) -> Set)
  _       <B= top     = One
  value x <B= value y = x <= y
  bottom  <B= _       = One
  _       <B= _       = Zero

  record _^_ (S T : (l u : Bound) -> Set) (l u : Bound) : Set where
    constructor pivoted
    field
      pivot : P
      lp  : S l (value pivot)
      pu : T (value pivot) u

  <!_!>OSO : SO -> ((l u : Bound) -> Set) -> ((l u : Bound) -> Set)
  <! qR !>OSO     R     = R
  <! q1 !>OSO     R l u = l <B= u
  <! S q+ T !>OSO R l u = <! S !>OSO R l u + <! T !>OSO R l u
  <! S q^ T !>OSO R     = <! S !>OSO R     ^ <! T !>OSO R

  data MuOSO (F : SO) (l u : Bound) : Set where
    la_ra : <! F !>OSO (MuOSO F) l u -> MuOSO F l u

  OTree = MuOSO qTree
  OInterval = MuOSO qInterval

  pattern leaf lu = la inl lu ra
  pattern node p lt rt = la inr (pivoted p lt rt) ra

  pattern interval p lp pu = la pivoted p lp pu ra

  tree : {l u : Bound}
    -> {F : SO}
    -> MuOSO F l u
    -> OTree l u
  tree {l} {u} {F} la f ra = go F f
    where
    go : {l u : Bound}
      -> (G : SO)
      -> <! G !>OSO (MuOSO F) l u
      -> OTree l u
    go qR f = tree f
    go q1 lu = leaf lu
    go (S q+ T) (inl s) = go S s
    go (S q+ T) (inr t) = go T t
    go (S q^ T) (pivoted pivot lp pu) = node pivot (go S lp) (go T pu)

  insert : {l u : Bound}
    -> OInterval l u
    -> OTree l u
    -> OTree l u
  insert (interval p lp pu) (leaf lu) = node p (leaf lp) (leaf pu)
  insert (interval p lp pu) (node x lt rt) with compare p x
  ... | x<=y px = node x (insert (interval p lp px) lt) rt
  ... | y<=x xp = node x lt (insert (interval p xp pu) rt)


