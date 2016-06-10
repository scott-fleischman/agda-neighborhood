module Relation where

data Zero : Set where
record One : Set where constructor it

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

data <$_$>D (P : Set) : Set where
  top  :       <$ P $>D
  tb   : P ->  <$ P $>D
  bot  :       <$ P $>D

record Σ (S : Set) (T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ
_×_ : Set -> Set -> Set
S × T = Σ S \ _ -> T
infixr 5 _×_ _,_

REL : Set -> Set1
REL P = P × P -> Set

data _+_ (S T : Set) :  Set where
  inl : S -> S + T
  inr : T -> S + T
infixr 4 _+_

OWOTO : forall {P}(L : REL P) -> REL P
OWOTO L (x , y) = <P L (x , y) P> + <P L (y , x) P>

pattern le  = inl !
pattern ge  = inr !

<$_$>F <^_^>P : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     , top)   = One
<$ L $>F (tb x  , tb y)  = L (x , y)
<$ L $>F (bot   , _)     = One
<$ L $>F (_     , _)     = Zero
<^ L ^>P xy = <P <$ L $>F xy P>

Never Always : {I : Set} -> I -> Set
Never   i = Zero
Always  i = One

_-+-_ _-*-_ _>>_ : {I : Set} ->
  (I -> Set) -> (I -> Set) -> I -> Set
(S -+- T)  i = S i + T i
(S -*- T)  i = S i × T i
(S >> T)   i = S i -> T i
infixr 3 _-+-_ ; infixr 4 _-*-_ ; infixr 2 _>>_

[_] : {I : Set} -> (I -> Set) -> Set
[ F ] = forall {i} -> F i

mytest : forall {I}{S T : I -> Set} -> [ S >> S -+- T ]
mytest = inl

_^_ : forall {P} -> REL <$ P $>D -> REL <$ P $>D -> REL <$ P $>D
_^_ {P} S T (l , u) = Σ P \ p -> S (l , tb p) × T (tb p , u)

<$_$>II : forall {P}(L : REL P) -> REL <$ P $>D
<$ L $>II = <^ L ^>P ^ <^ L ^>P
pattern <$_$>ii p = p , ! , !

module BinarySearchTreeWorks
  (P : Set)
  (L : REL P)
  (owoto : forall x y -> OWOTO L (x , y))
  where

  data BST (lu : <$ P $>D × <$ P $>D) : Set where
    leaf   :  BST lu
    pnode  :  ((<^ L ^>P -*- BST) ^ (<^ L ^>P -*- BST) >> BST) lu
  pattern node lt p rt = pnode (p , (! , lt) , (! , rt))

  insert2 :  [ <$ L $>II >> BST >> BST ]
  insert2 <$ y $>ii leaf            = node leaf y leaf
  insert2 <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = node (insert2 <$ y $>ii lt) p rt
  ... | ge  = node lt p (insert2 <$ y $>ii rt)

  rotR : [ BST >> BST ]
  rotR (node (node lt m mt) p rt)
    = {!!} -- node lt m (node mt p rt)
  rotR t = t

module BinarySearchTreeBest
  (P : Set)
  (L : REL P)
  (owoto : forall x y -> OWOTO L (x , y))
  where

  data BST (lu : <$ P $>D × <$ P $>D) : Set where
    pleaf  :  (<^ L ^>P >> BST) lu
    pnode  :  (BST ^ BST >> BST) lu

  pattern leaf          = pleaf !
  pattern node lt p rt  = pnode (p , lt , rt)

  insert :  [ <$ L $>II >> BST >> BST ]
  insert <$ y $>ii leaf = node leaf y leaf
  insert <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = node (insert <$ y $>ii lt) p rt
  ... | ge  = node lt p (insert <$ y $>ii rt)

  rotR : [ BST >> BST ]
  rotR (node (node lt m mt) p rt)
     = node lt m (node mt p rt)
  rotR t = t

  data OList (lu : <$ P $>D × <$ P $>D) : Set where
    nil   :  (<^ L ^>P >> OList) lu
    cons  :  (<^ L ^>P ^ OList >> OList) lu 

module BestNat where
  data Nat : Set where
    ze : Nat
    su : Nat -> Nat
  {-# BUILTIN NATURAL Nat #-}

  Le : REL Nat
  Le (x , y) = x <= y where
    _<=_ : Nat -> Nat -> Set
    ze    <= y     =  One
    su x  <= ze    =  Zero
    su x  <= su y  =  x <= y

  nowoto : forall x y -> OWOTO Le (x , y)
  nowoto ze      y       = le
  nowoto (su x)  ze      = ge
  nowoto (su x)  (su y)  = nowoto x y

  open BinarySearchTreeBest Nat Le nowoto

  ex1 : BST (bot , top)
  ex1 = leaf

  ex2 : BST (tb 9 , tb 9)
  ex2 = node leaf 9 leaf

  ex3 : BST (bot , top)
  ex3 = node (node leaf 8 leaf) 9 leaf

  ex4 : BST (bot , top)
  ex4 = insert <$ 9 $>ii leaf

  ex5 : BST (bot , top)
  ex5 = insert <$ 9 $>ii (insert <$ 6 $>ii (insert <$ 12 $>ii leaf))
