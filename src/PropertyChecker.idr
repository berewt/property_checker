module PropertyChecker

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

Nuf : Vect k Type -> Type -> Type
Nuf [] t = t
Nuf (x::xs) t = Nuf xs (x -> t)

apply : Nuf xs a -> HVect xs -> a
apply x [] = x
apply f (x :: xs) = apply f xs x


test : Path input output initial -> Nuf initial Bool -> HVect input -> Bool
test [] f x = apply f x
test ((Any g) :: xs) f z = any (test xs f) (map (:: z) (g z))
test ((All g) :: xs) f z = all (test xs f) (map (:: z) (g z))

test' : Path [()] output initial -> Nuf initial Bool -> Bool
test' p f = test p f [()]

