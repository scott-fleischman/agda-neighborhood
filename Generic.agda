module Generic where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

_o_ : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
      (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
(f o g) x = f (g x)
infixr 3 _o_

id : {A : Set} -> A -> A
id a = a

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _/_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 5 _*_ _/_

REL : Set -> Set1
REL P = P * P -> Set

data _+_ (S T : Set) :  Set where
  inl : S -> S + T ;    inr : T -> S + T
infixr 4 _+_

OWOTO : forall {P}(L : REL P) -> REL P
OWOTO L (x / y) = <P L (x / y) P> + <P L (y / x) P>

pattern le  = inl !
pattern ge  = inr !

data <$_$>D (P : Set) : Set where
  top  :       <$ P $>D ; tb   : P ->  <$ P $>D ;  bot  :       <$ P $>D

<$_$>F <^_^>P : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     / top)   = One
<$ L $>F (tb x  / tb y)  = L (x / y)
<$ L $>F (bot   / _)     = One
<$ L $>F (_     / _)     = Zero
<^ L ^>P xy = <P <$ L $>F xy P>

_-+-_ _-*-_ _>>_ : {I : Set} ->
  (I -> Set) -> (I -> Set) -> I -> Set
(S -+- T)  i = S i + T i
(S -*- T)  i = S i * T i
(S >> T)   i = S i -> T i
infixr 3 _-+-_ ; infixr 4 _-*-_ ; infixr 2 _>>_

[_] : {I : Set} -> (I -> Set) -> Set
[ F ] = forall {i} -> F i

_^_ : forall {P} -> REL <$ P $>D -> REL <$ P $>D -> REL <$ P $>D
_^_ {P} S T (l / u) = Sg P \ p -> S (l / tb p) * T (tb p / u)

pattern _\\_\\_ s p t = p / s / t
infixr 5 _\\_\\_ 

data JJ : Set where
  qR qP q1   : JJ
  _q+_ _q*_  : JJ -> JJ -> JJ
infixr 4 _q+_
infixr 5 _q*_

<!_!>JJ : JJ -> Set -> Set -> Set
<! qR !>JJ      R P = R
<! qP !>JJ      R P = P
<! q1 !>JJ      R P = One
<! S q+ T !>JJ  R P = <! S !>JJ R P + <! T !>JJ R P
<! S q* T !>JJ  R P = <! S !>JJ R P * <! T !>JJ R P

data MuJJ (F : JJ)(P : Set) : Set where
  la_ra : <! F !>JJ (MuJJ F P) P -> MuJJ F P

record Applicative (H : Set -> Set) : Set1 where
  field
    pure  : forall {X} -> X -> H X
    ap    : forall {S T} -> H (S -> T) -> H S -> H T
open Applicative

traverse : forall {H F A B} -> Applicative H ->
  (A -> H B) -> MuJJ F A -> H (MuJJ F B)
traverse {H}{F}{A}{B} AH h t = go qR t where
  pur = pure AH ; _<*>_ = ap AH
  go : forall G ->
    <! G !>JJ (MuJJ F A) A -> H (<! G !>JJ (MuJJ F B) B)
  go qR        la t ra  = pur la_ra <*> go F t
  go qP        a        = h a
  go q1        it       = pur it
  go (S q+ T)  (inl s)  = pur inl <*> go S s
  go (S q+ T)  (inr t)  = pur inr <*> go T t
  go (S q* T)  (s / t)  = (pur _/_ <*> go S s) <*> go T t

idApp : Applicative (\ X -> X)
idApp = record {pure = id ; ap = id}

map : forall {F A B} ->
  (A -> B) -> MuJJ F A -> MuJJ F B
map = traverse idApp

record Monoid (X : Set) : Set where
  field neutral : X ;  combine : X -> X -> X
  monApp : Applicative (\ _ -> X)
  monApp = record
    {pure = \ _ -> neutral ; ap = combine}
  crush : forall {P F} -> (P -> X) -> MuJJ F P -> X
  crush = traverse {B = Zero} monApp
open Monoid

compMon : forall {X} -> Monoid (X -> X)
compMon = record
  {neutral = id ; combine = \ f g -> f o g}

foldr : forall {F A B} ->
  (A -> B -> B) -> B -> MuJJ F A -> B
foldr f b t = crush compMon f t b

data SO : Set where
  qR q1      : SO
  _q+_ _q^_  : SO -> SO -> SO
infixr 5 _q^_

<!_!>SO : SO -> JJ
<! qR !>SO      = qR
<! q1 !>SO      = q1
<! S q+ T !>SO  = <! S !>SO q+ <! T !>SO
<! S q^ T !>SO  = <! S !>SO q* qP q* <! T !>SO

MuSO : SO -> Set -> Set
MuSO F P = MuJJ <! F !>SO P

qListSO qTreeSO qIntervalSO : SO
qListSO      = q1 q+ (q1 q^ qR)
qTreeSO      = q1 q+ (qR q^ qR)
qIntervalSO  = q1 q^ q1

treeSO : forall {P F} -> MuSO F P -> MuSO qTreeSO P
treeSO {P}{F} la f ra = go F f where
  go : forall G -> <! <! G !>SO !>JJ (MuSO F P) P -> MuSO qTreeSO P
  go qR        f            = treeSO f
  go q1        it           = la inl it ra
  go (S q+ T)  (inl s)      = go S s
  go (S q+ T)  (inr t)      = go T t
  go (S q^ T)  (s / p / t)  = la inr (go S s / p / go T t) ra

<!_!>OSO : SO -> forall {P} -> REL <$ P $>D -> REL P -> REL <$ P $>D
<! qR !>OSO       R L = R
<! q1 !>OSO       R L = <^ L ^>P
<! S q+ T !>OSO   R L = <! S !>OSO R L -+- <! T !>OSO R L
<! S q^ T !>OSO   R L = <! S !>OSO R L ^ <! T !>OSO R L

data MuOSO  (F : SO){P : Set}(L : REL P)
            (lu : <$ P $>D * <$ P $>D) : Set where
  la_ra : <! F !>OSO (MuOSO F L) L lu -> MuOSO F L lu

<$_$>T <$_$>I : forall {P} -> REL P -> REL <$ P $>D

<$ L $>T  = MuOSO qTreeSO      L
pattern leaf          = la inl ! ra
pattern node lp p pu  = la inr (lp \\ p \\ pu) ra

<$ L $>I  = MuOSO qIntervalSO  L
pattern <$_$>ic p = la (p / ! / !) ra

treeOSO :  forall {P F}{L : REL P} -> [ MuOSO F L >> <$ L $>T ]
treeOSO {P}{F}{L} la f ra = go F f where
  go : forall G -> [ <! G !>OSO (MuOSO F L) L >> <$ L $>T ]
  go qR        f              = treeOSO f
  go q1        !              = leaf
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = node (go S s) p (go T t)

module BinarySearchTreeGen
  {P : Set}(L : REL P)(owoto : forall x y -> OWOTO L (x / y)) where

  insert2 : [ <$ L $>I >> <$ L $>T >> <$ L $>T ]
  insert2 <$ y $>ic leaf            = node leaf y leaf
  insert2 <$ y $>ic (node lt p rt)  with owoto y p
  ... | le  = node (insert2 <$ y $>ic lt) p rt
  ... | ge  = node lt p (insert2 <$ y $>ic rt)

  makeTree : forall {F} -> MuJJ F P -> <$ L $>T (bot / top)
  makeTree = foldr (\ p -> insert2 <$ p $>ic) leaf
