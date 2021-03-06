module Generic where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

_:-_ : forall {P T} -> <P P P> -> (P => T) -> T
! :- t = t

magic :  {X : Set} -> Zero => X
magic {{()}}

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

_o_ : {A : Set} {B : A -> Set} {C : (a : A) -> B a -> Set}
  (f : {a : A} (b : B a) -> C a b)
  (g : (a : A) -> B a)
  -> (a : A)
  -> C a (g a)
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

<$_$>+ : forall {P} -> REL P -> REL <$ P $>D
<$ L $>+ = MuOSO qListSO L

pattern nil        = la inl ! ra
pattern _//_ x xs  = la inr (x / ! / xs) ra
infixr 6 _//_

module MergeSO where
  postulate
    P : Set
    L : REL P
    owoto : forall x y -> OWOTO L (x / y)

  mergeSO : [ <$ L $>+ >> <$ L $>+ >> <$ L $>+ ]
  mergeSO          nil        = id
  mergeSO {l / u}  (x // xs)  = go where
    go :  forall {l}{{_ : <$ L $>F (l / tb x)}} -> (<$ L $>+ >> <$ L $>+) (l / u)
    go nil        = x // xs
    go (y // ys)  with owoto x y
    ... | le  = x // mergeSO xs (y // ys)
    ... | ge  = y // go ys

  olistMon : forall {lu} -> <$ L $>F lu => Monoid (<$ L $>+ lu)
  olistMon = record {neutral = nil ; combine = mergeSO}

  mergeJJ : forall {F} -> MuJJ F P -> <$ L $>+ (bot / top)
  mergeJJ = crush olistMon \ p -> p // nil

  qLTree : JJ
  qLTree = (q1 q+ qP) q+ qR q* qR

  pattern none      = la inl (inl it) ra
  pattern one p     = la inl (inr p) ra
  pattern fork l r  = la inr (l / r) ra

  twistIn : P -> MuJJ qLTree P -> MuJJ qLTree P
  twistIn p none        = one p
  twistIn p (one q)     = fork (one p) (one q)
  twistIn p (fork l r)  = fork (twistIn p r) l

  mergeSort : forall {F} -> MuJJ F P -> <$ L $>+ (bot / top)
  mergeSort = mergeJJ o foldr twistIn none

sandwich :  forall {P}{L : REL P} -> [ (<$ L $>+ ^ <$ L $>+) >> <$ L $>+ ]
sandwich (nil      \\ p \\ ys)  = p // ys
sandwich (x // xs  \\ p \\ ys)  = x // sandwich (xs \\ p \\ ys)

flattenT : forall {P}{L : REL P} -> [ <$ L $>T >> <$ L $>+ ]
flattenT leaf          = nil
flattenT (node l p r)  = sandwich (flattenT l \\ p \\ flattenT r)

flattenOSO : forall {P}{L : REL P}{F} -> [ MuOSO F L >> <$ L $>+ ]
flattenOSO = flattenT o treeOSO

infixr 8 _+++_
Replacement : forall {P} -> REL P -> REL <$ P $>D
Replacement L (n / u) = forall {m} -> <$ L $>F (m / n) => <$ L $>+ (m / u)

_+++_ : forall {P}{L : REL P}{l n u} ->
  <$ L $>+ (l / n) -> Replacement L (n / u) -> <$ L $>+ (l / u)
nil        +++ ys = ys
(x // xs)  +++ ys = x // xs +++ ys

fflapp : forall {P}{L : REL P}{F}{l n u} ->
  MuOSO F L (l / n) ->  Replacement L (n / u) -> <$ L $>+ (l / u)
fflapp {P}{L}{F}{u = u} t ys = go qR t ys where
  go :   forall {l n} G -> <! G !>OSO (MuOSO F L) L (l / n) ->
          Replacement L (n / u) -> <$ L $>+ (l / u)
  go qR        la t ra        ys  = go F t ys
  go q1        !              ys  = ys
  go (S q+ T)  (inl s)        ys  = go S s ys
  go (S q+ T)  (inr t)        ys  = go T t ys
  go (S q^ T)  (s \\ p \\ t)  ys  = go S s (p // go T t ys)

flatten : forall {P}{L : REL P}{F} -> [ MuOSO F L >> <$ L $>+ ]
flatten t = fflapp t nil

data IO (I : Set) : Set where
  qR         : I -> IO I
  q0 q1      : IO I
  _q+_ _q^_  : IO I -> IO I -> IO I

<!_!>IO :  forall {I P} -> IO I ->
           (I -> REL <$ P $>D) -> REL P -> REL <$ P $>D
<! qR i !>IO    R L  = R i
<! q0 !>IO      R L  = \ _ -> Zero
<! q1 !>IO      R L  = <^ L ^>P
<! S q+ T !>IO  R L  = <! S !>IO R L -+- <! T !>IO R L
<! S q^ T !>IO  R L  = <! S !>IO R L ^ <! T !>IO R L

data MuIO  {I P : Set}(F : I -> IO I)(L : REL P)
           (i : I)(lu : <$ P $>D * <$ P $>D) : Set where
  la_ra : <! F i !>IO (MuIO F L) L lu -> MuIO F L i lu

qListIO qTreeIO qIntervalIO : One -> IO One
qListIO      _ = q1 q+ (q1 q^ qR it)
qTreeIO      _ = q1 q+ (qR it q^ qR it)
qIntervalIO  _ = q1 q^ q1

<$_$>i+ <$_$>iT <$_$>iI : forall {P} -> REL P -> REL <$ P $>D
<$ L $>i+  = MuIO qListIO      L it
<$ L $>iT  = MuIO qTreeIO      L it
<$ L $>iI  = MuIO qIntervalIO  L it

pattern <$_$>io p = la p / ! / ! ra

qVecIO : Nat -> IO Nat
qVecIO ze      = q1
qVecIO (su n)  = q1 q^ qR n

qEvenIO : Nat -> IO Nat
qEvenIO ze           = q1
qEvenIO (su ze)      = q0
qEvenIO (su (su n))  = q1 q^ q1 q^ qR n

treeIO :  forall {I P F}{L : REL P}{i : I} ->
  [ MuIO F L i >> <$ L $>iT ]
pattern leif = la inl ! ra
pattern nodi lp p pu = la inr (p / lp / pu) ra
treeIO {F = F}{L = L}{i = i} la t ra = go (F i) t where
  go : forall G -> [ <! G !>IO (MuIO F L) L >> <$ L $>iT ]
  go (qR i)    t              = treeIO t
  go q0        ()
  go q1        !              = leif
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = nodi (go S s) p (go T t)

flattenIO :  forall {I P F}{L : REL P}{i : I} ->
  [ MuIO F L i >> <$ L $>i+ ]
pattern _/i/_ x xs = la inr (x / ! / xs) ra
flattenIO {I}{P}{F}{L}{i}{l / u} la t ra = go (F i) t la inl ! ra where
  go : forall G {l n} -> <! G !>IO (MuIO F L) L (l / n) ->
       (forall {m} -> <$ L $>F (m / n) => <$ L $>i+ (m / u)) ->
       <$ L $>i+ (l / u)
  go (qR i)    la t ra        ys = go (F i) t ys
  go q0        ()             ys
  go q1        !              ys = ys
  go (S q+ T)  (inl s)        ys = go S s ys
  go (S q+ T)  (inr t)        ys = go T t ys
  go (S q^ T)  (s \\ p \\ t)  ys = go S s (p /i/ go T t ys)


q23TIO : Nat -> IO Nat
q23TIO ze      = q1
q23TIO (su h)  = qR h q^ (qR h q+ (qR h q^ qR h))

<$_$>23 : forall {P}(L : REL P) -> Nat -> REL <$ P $>D
<$ L $>23 = MuIO q23TIO L

pattern no0               = la ! ra
pattern no2 lt p rt       = la p / lt / inl rt ra
pattern no3 lt p mt q rt  = la p / lt / inr (q / mt / rt) ra
pattern via p = p / ! / !
pattern _-\_ t p = p / t / !

module Tree23
  {P : Set}(L : REL P)(owoto : forall x y -> OWOTO L (x / y)) where

  ins23 :  forall h {lu} -> <$ L $>iI lu -> <$ L $>23 h lu ->
           <$ L $>23 h lu +
           Sg P \ p -> <$ L $>23 h (fst lu / tb p) * <$ L $>23 h (tb p / snd lu)
  ins23 ze      <$ y $>io no0 = inr (la ! ra \\ y \\ la ! ra)
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra with owoto y p
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra | le
    with ins23 h <$ y $>io lt
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra | le
    | inl lt'                = inl la lt' \\ p \\ rest ra
  ins23 (su h)  <$ y $>io (no2 lt p rt)       | le
    | inr (llt \\ r \\ lrt)  = inl (no3 llt r lrt p rt)
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | le
    | inr (llt \\ r \\ lrt)  = inr (no2 llt r lrt \\ p \\ no2 mt q rt)
  ins23 (su h)  <$ y $>io (no2 lt p rt) | ge  with ins23 h <$ y $>io rt
  ins23 (su h)  <$ y $>io (no2 lt p rt) | ge  | rt' = inl la lt \\ p \\ rt' ra
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt) | ge  with owoto y q
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   le
    with ins23 h <$ y $>io mt
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   le
    | inl mt'                = inl (no3 lt p mt' q rt)
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   le
    | inr (mlt \\ r \\ mrt)  = inr (no2 lt p mlt \\ r \\ no2 mrt q rt)

  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   ge
    with ins23 h <$ y $>io rt
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   ge
    | inl rt'                = inl (no3 lt p mt q rt')
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   ge
    | inr (rlt \\ r \\ rrt)  = inr (no2 lt p mt \\ q \\ no2 rlt r rrt)

  T23 = Sg Nat \ h -> <$ L $>23 h (bot / top)

  insert2 : P -> T23 -> T23
  insert2 p (h / t) with ins23 h <$ p $>io t
  ... | inl t'               = h     / t'
  ... | inr (lt \\ r \\ rt)  = su h  / no2 lt r rt

  sort : forall {F} -> MuJJ F P -> <$ L $>i+ (bot / top)
  sort = flattenIO o snd o foldr insert2 (ze / no0)


  data _==_ {X : Set}(x : X) : X -> Set where
    it : x == x
  infix 6 _==_

  module Delete23 (
    trans : forall {x} y {z} -> L (x / y) => L (y / z) => <P L (x / z) P>
    )(
    eq? : (x y : P) -> x == y + (x == y -> Zero)
    ) where

    transTB : [ (<^ L ^>P ^ <^ L ^>P) >> <^ L ^>P ]
    transTB {_     / top}   _         = !
    transTB {bot   / bot}   _         = !
    transTB {bot   / tb u}  _         = !
    transTB {top   / _}     (via _)   = magic
    transTB {tb l  / tb u}  (via p)   = trans p :- !
    transTB {tb l  / bot}   (via _)   = magic

    Del23 Short23 : Nat -> REL <$ P $>D
    Del23    h      lu  =  Short23 h lu + <$ L $>23 h lu
    Short23  ze     lu  =  Zero
    Short23  (su h) lu  =  <$ L $>23 h lu

    Re2 :  Nat -> REL <$ P $>D
    Re2 h =  Short23 (su h) -+- (<$ L $>23 h ^ <$ L $>23 h)

    d2t :  forall {h} -> [ (Del23 h ^ <$ L $>23 h) >> Re2 h ]
    d2t {h}     (inr lp  \\ p \\ pu)           = inr (lp \\ p \\ pu)
    d2t {ze}    (inl ()  \\ p \\ pu)
    d2t {su h}  (inl lp  \\ p \\ no2 pq q qu)  = inl (no3 lp p pq q qu)
    d2t {su h}  (inl lp  \\ p \\ no3 pq q qr r ru)
      = inr (no2 lp p pq \\ q \\ no2 qr r ru)

    t2d :  forall {h} -> [ (<$ L $>23 h ^ Del23 h) >> Re2 h ]
    t2d {h}     (lp \\ p \\ inr pu)           = inr (lp \\ p \\ pu)
    t2d {ze}    (lp \\ p \\ inl ())
    t2d {su h}  (no2 ln n np \\ p \\ inl pu)  = inl (no3 ln n np p pu)
    t2d {su h}  (no3 lm m mn n np  \\ p \\ inl pu)
      = inr (no2 lm m mn \\ n \\ no2 np p pu)

    rd : forall {h} -> [ Re2 h >> Del23 (su h) ]
    rd (inl s)                = (inl s)
    rd (inr (lp \\ p \\ pu))  = inr (no2 lp p pu)

    r3t :  forall {h} -> [ (Re2 h ^ <$ L $>23 h) >> Del23 (su h) ]
    r3t (inr (lm \\ m \\ mp) \\ p \\ pu)    = inr (no3 lm m mp p pu)
    r3t (inl lp \\ p \\ pu)                 = inr (no2 lp p pu)

    t3r :  forall {h} -> [ (<$ L $>23 h ^ Re2 h) >> Del23 (su h) ]
    t3r (lp \\ p \\ inr (pq \\ q \\ qu))    = inr (no3 lp p pq q qu)
    t3r (lp \\ p \\ inl pu)                 = inr (no2 lp p pu)

    extr : forall {h} -> [ <$ L $>23 (su h) >> (Del23 (su h) ^ <^ L ^>P) ]
    extr {ze} (no2 lr r no0)        = inl lr -\ r
    extr {ze} (no3 lp p pr r no0)   = inr (no2 lp p pr) -\ r
    extr {su h} (no2 lp p pu)       with extr pu
    ... | pr -\ r = rd (t2d (lp \\ p \\ pr)) -\ r
    extr {su h} (no3 lp p pq q qu)  with extr qu
    ... | qr -\ r = t3r (lp \\ p \\ t2d (pq \\ q \\ qr)) -\ r

    delp : forall {h} -> [ (<$ L $>23 h ^ <$ L $>23 h) >> Re2 h ]
    delp {ze}    {lu}  (no0 \\ p \\ no0) = transTB {lu} (via p) :- inl no0
    delp {su h}        (lp \\ p \\ pu) with extr lp
    ... | lr -\ r = d2t (lr \\ r \\ weak pu) where
      weak : forall {h u} -> <$ L $>23 h (tb p / u) -> <$ L $>23 h (tb r / u)
      weak {ze} {u}  no0 = transTB {tb r / u} (via p) :- no0
      weak {su h} la pq \\ q \\ qu ra = la weak pq \\ q \\ qu ra

    del23 : forall {h} -> [ <$ L $>iI >> <$ L $>23 h >> Del23 h ]
    del23 {ze}   _           no0                  = inr no0
    del23 {su h} <$ y $>io   la lp \\ p \\ pu ra  with eq? y p
    del23 {su h} <$ .p $>io  (no2 lp p pu)        | inl it
      = rd (delp (lp \\ p \\ pu))
    del23 {su h} <$ .p $>io  (no3 lp p pq q qu)   | inl it
      = r3t (delp (lp \\ p \\ pq) \\ q \\ qu)
    del23 {su h} <$ y $>io   la lp \\ p \\ pu ra  | inr _ with owoto y p
    del23 {su h} <$ y $>io   (no2 lp p pu)        | inr _ | le
      = rd (d2t (del23 <$ y $>io lp \\ p \\ pu))
    del23 {su h} <$ y $>io   (no2 lp p pu)        | inr _ | ge
      = rd (t2d (lp \\ p \\ del23 <$ y $>io pu))
    del23 {su h} <$ y $>io   (no3 lp p pq q qu)   | inr _ | le
      = r3t (d2t (del23 <$ y $>io lp \\ p \\ pq) \\ q \\ qu)
    del23 {su h} <$ y $>io   (no3 lp p pq q qu)   | inr _ | ge with eq? y q
    del23 {su h} <$ .q $>io  (no3 lp p pq q qu)   | inr _ | ge | inl it
      = t3r (lp \\ p \\ delp (pq \\ q \\ qu))
    ... | inr _ with owoto y q
    ... | le = r3t (t2d (lp \\ p \\ del23 <$ y $>io pq) \\ q \\ qu)
    ... | ge = t3r (lp \\ p \\ t2d (pq \\ q \\ del23 <$ y $>io qu))
