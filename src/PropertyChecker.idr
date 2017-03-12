module PropertyChecker

import Data.Fun
import Data.HVect

%default total

data Quantifier : Vect n Type -> Type -> Type where
  Any : (HVect input -> List output) -> Quantifier input output
  All : (HVect input -> List output) -> Quantifier input output

forall : List a -> Quantifier xs a
forall = All . const

exists : List a -> Quantifier xs a
exists = Any . const

fromContext : (a -> List b) -> {auto p: Elem a xs} -> HVect xs -> List b
fromContext f ctx = f $ get ctx

data Path : (input : Vect i Type)
          -> (output : Vect j Type)
          -> (initial : Vect k Type)
          -> Type where
  Nil  : Path input [] input
  (::) : Quantifier input t -> Path (t::input) output a -> Path input (t::output) a

Path' : Type -> Vect n Type -> Type
Path' start output = Path [start] output (reverse (start::output))

Path_ : Vect n Type -> Type
Path_ output = Path [Unit] output (reverse (Unit::output))

private
testStep : Path input output initial -> Fun output Bool -> HVect input -> Bool
testStep [] x _ = x
testStep ((Any g) :: xs) f inp = any (\params => testStep xs (f $ index 0 params) params) (map (::inp) (g inp))
testStep ((All g) :: xs) f inp = all (\params => testStep xs (f $ index 0 params) params) (map (::inp) (g inp))

test : Path' a output -> Fun output Bool -> a -> Bool
test p f x = testStep p f [x]

test_ : Path_ output -> Fun output Bool -> Bool
test_ p f = testStep p f [()]
