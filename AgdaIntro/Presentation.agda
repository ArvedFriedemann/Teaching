{-# OPTIONS --type-in-type #-}
module Presentation where

module Basics where
  data Subject : Set where
    Person : Subject
    Bird : Subject

  data Determiner : Set where
    the : Determiner

  data Object : Set where
    _Car : Determiner -> Object
    _Corn : Determiner -> Object

  infix 10 _drives_
  infix 10 _eats_
  data Sentence : Set where
    _drives_ : Subject -> Object -> Sentence
    _eats_ : Subject -> Object -> Sentence

  _ : Sentence
  _ = Person drives the Car

  _ : Sentence
  _ = Bird drives the Corn

  data Subjekt : Set where
    Mensch : Subjekt
    Vogel : Subjekt

  data Begleiter : Set where
    das : Begleiter
    den : Begleiter

  data Objekt : Set where
    _Auto : Begleiter -> Objekt
    _Mais : Begleiter -> Objekt

  infix 10 _fährt_
  infix 10 _isst_
  data Satz : Set where
    _fährt_ : Subjekt -> Objekt -> Satz
    _isst_ : Subjekt -> Objekt -> Satz

  translate : Satz -> Sentence
  translate (Mensch fährt (das Auto)) = Person drives the Car
  translate (Mensch fährt (den Mais)) = Person drives the Corn
  translate (Vogel fährt (das Auto)) = Bird drives the Car
  translate (Vogel fährt (den Mais)) = Bird drives the Corn
  --...
  translate _ = Person drives (the Car) --anything

  transSubjekt : Subjekt -> Subject
  transSubjekt Mensch = Person
  transSubjekt Vogel = Bird

  transObjekt : Objekt -> Object
  transObjekt (x Auto) = the Car
  transObjekt (x Mais) = the Corn

  transSatz : Satz -> Sentence
  transSatz (x fährt y) = (transSubjekt x) drives (transObjekt y)
  transSatz (x isst y) = (transSubjekt x) eats (transObjekt y)

module Advanced where
  open import Data.List renaming (_∷_ to _::_)
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat renaming (ℕ to Nat) hiding (_<_)

  _orB_ : Bool -> Bool -> Bool
  false orB false = false
  _ orB _ = true

  data Token : Set where
    NounMasc : Token
    NounFemn : Token
    NounNeut : Token

  _=T=_ : Token -> Token -> Bool
  _=T=_ NounMasc NounMasc = true
  _=T=_ NounFemn NounFemn = true
  _=T=_ NounNeut NounNeut = true
  _=T=_ _ _ = false

  record Eq (A : Set) : Set where
    field
      _==_ : A -> A -> Bool

  open Eq {{...}}

  data _===_ {A : Set} (a : A) : A -> Set where
    refl : a === a

  data Unit : Set where
    unit : Unit

  instance
    _ : Unit
    _ = unit

    _ : Eq Token
    _ = record { _==_ = _=T=_ }

  data Bot : Set where

  is : Bool -> Set
  is true = Unit
  is false = Bot

  _elem_ : {A : Set} -> {{Eq A}} -> A -> List A -> Bool
  x elem [] = false
  x elem (y :: ys) = (x == y) orB (x elem ys)

  data Begleiter (ctx : List Token) : Set where
    der : {{is (NounMasc elem ctx)}} -> Begleiter ctx
    die : {{is (NounFemn elem ctx)}} -> Begleiter ctx
    das : {{is (NounNeut elem ctx)}} -> Begleiter ctx

  data Subjekt (ctx : List Token) : Set where
    _Person : Begleiter (NounFemn :: ctx) -> Subjekt ctx
    _Vogel : Begleiter (NounMasc :: ctx) -> Subjekt ctx

  _ : Subjekt []
  _ = die Person


  ---------------------------------------------------------------
  --Algorithms
  ---------------------------------------------------------------

  record Ord (A : Set) : Set where
    field
      _<_ : A -> A -> Bool

  open Ord {{...}}


  repeat_for_times-on_ : {A : Set} -> (A -> A) -> Nat -> A -> A
  repeat_for_times-on_ _ 0 a = a
  repeat_for_times-on_ f (suc n) a = repeat f for n times-on (f a)

  module _ {A : Set} where

    {-# TERMINATING #-}
    bubble-once : {{Ord A}} -> List A -> List A
    bubble-once [] = []
    bubble-once (x :: []) = x :: []
    bubble-once (x :: y :: ys) with x < y
    ...| true  = x :: bubble-once (y :: ys)
    ...| false = y :: bubble-once (x :: ys)

    bubblesort : {{Ord A}} -> List A -> List A
    bubblesort lst = repeat bubble-once for (length lst * length lst) times-on lst
