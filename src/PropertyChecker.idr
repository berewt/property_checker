module PropertyChecker

import Data.Fun
import Data.HVect

%default total
%access export

||| A Quantifier defines how a selection will be handeld in a test.
||| It is used in Tests to determine for which values a given property must hold.
||| The selection should output a list of element out of an HVect.
public export
data Quantifier : Vect n Type -> Type -> Type where
  ||| The Any quantifier indicates that te property must hold for
  ||| all the values of the selection.
  All : (selector : HVect input -> List output) -> Quantifier input output
  ||| The Any quantifier indicates that te property must hold for
  ||| at least one value of the selection.
  Any : (selector : HVect input -> List output) -> Quantifier input output

||| A helper that build an All quantifier that use a given selection instead of
||| using the context to build one.
allFrom : (selection: List a) -> Quantifier xs a
allFrom = All . const

||| A helper that build an Any quantifier that use a given selection instead of
||| using the context to build one.
anyFrom : List a -> Quantifier xs a
anyFrom = Any . const

||| A helper that creates a selection with a unique element
||| (uses an All quantifier).
raw : a -> Quantifier xs a
raw = All . const . pure

private
fromContext : (a -> List b) -> {auto p: Elem a xs} -> HVect xs -> List b
fromContext f ctx = f $ get ctx

||| An helper for a simple context-based All selection,
||| it extracts an arbitrary element from the expected type to build the
||| selection.
forall : (a -> List b) -> {auto p: Elem a xs} -> Quantifier xs b
forall f = All (fromContext f)

||| An helper for a simple context-based Any selection,
||| it extracts an arbitrary element from the expected type to build the
||| selection.
exists : (a -> List b) -> {auto p: Elem a xs} -> Quantifier xs b
exists f = Any (fromContext f)


||| Uninhabited type use to tag values
data AllMarker : Type -> Type
||| Uninhabited type use to tag values
data AnyMarker : Type -> Type


||| The internal representation of a Path, the type is very verbose and is not
||| intended to be used directly.
public export
data Path' : (input : Vect i Type)
          -> (output : Vect j Type)
          -> Type where
  Nil  : Path' input []
  (::) : Quantifier input t -> Path' (t::input) output -> Path' input (t::output)

public export
Path : Type -> Vect n Type -> Type
Path start output = Path' [start] output

public export
Path_ : Vect n Type -> Type
Path_ output = Path' [Unit] output


data Failure : Vect n Type -> Type where
  EmptyFailure : Failure []
  AnyFailure : Vect k (t, Failure xs) -> Failure (AnyMarker t :: xs)
  AllFailure : Vect k (t, Failure xs) -> Failure (AllMarker t :: xs)

public export
pathFailure : {output : Vect n Type} -> Path' input output -> Vect n Type
pathFailure [] = []
pathFailure (Any f :: p) {output = t :: _} = AnyMarker t :: (pathFailure p)
pathFailure (All f :: p) {output = t :: _} = AllMarker t :: (pathFailure p)

expandAll : t
         -> Failure xs
         -> Failure (AllMarker t :: xs)
expandAll x xs = AllFailure [(x, xs)]

expandAny : t
         -> Failure xs
         -> Failure (AnyMarker t :: xs)
expandAny x xs = AnyFailure [(x, xs)]

composeAll : Either (Failure (AllMarker ft :: fts)) Nat
          -> Either (Failure (AllMarker ft :: fts)) Nat
          -> Either (Failure (AllMarker ft :: fts)) Nat
composeAll (Left (AllFailure xs)) (Left (AllFailure ys)) =
  Left $ AllFailure (xs ++ ys)
composeAll (Left l) (Right _) = Left l
composeAll (Right _) (Left l) = Left l
composeAll (Right x) (Right y) = Right (x + y)

composeAny : Either (Failure (AnyMarker ft :: fts)) Nat
          -> Either (Failure (AnyMarker ft :: fts)) Nat
          -> Either (Failure (AnyMarker ft :: fts)) Nat
composeAny (Left (AnyFailure xs)) (Left (AnyFailure ys)) =
  Left $ AnyFailure (xs ++ ys)
composeAny (Left _) (Right r) = Right r
composeAny (Right r) (Left _) = Right r
composeAny (Right x) (Right y) = Right 1


public export
data Test : Type -> Type where
  MkTest : (p : Path a output) -> Fun output Bool -> Test a

public export
testFailure : Test a -> Type
testFailure (MkTest p x) = Failure (pathFailure p)

public export
Test_ : Type
Test_ = Test Unit

private
testStep : (p : Path' input output)
        -> Fun output Bool
        -> HVect input
        -> Either (Failure (pathFailure p)) Nat
testStep [] b _ = if b then Right 1 else Left EmptyFailure
testStep ((Any g) :: p) f previous =
  let selection = g previous
      rec = map (\s => either (Left . expandAny s)
                              Right
                              (testStep p (f s) (s::previous)))
                selection
  in foldl composeAny (Left (AnyFailure [])) rec
testStep ((All g) :: p) f previous =
  let selection = g previous
      rec = map (\s => either (Left . expandAll s)
                              Right
                              (testStep p (f s) (s::previous)))
                selection
  in foldl composeAll (Right 0) rec

test : (t : Test a) -> a ->  Either (testFailure t) Nat
test (MkTest p f) x = testStep p f [x]

test_ : (t : Test_) -> Either (testFailure t) Nat
test_ t = test t ()


namespace testGroup

  public export
  data TestGroup : Nat -> Type -> Type where
      Nil  : TestGroup Z a
      (::) : Test a -> TestGroup n a -> TestGroup (S n) a

  TestGroup_ : Nat -> Type
  TestGroup_ n = TestGroup n ()

  public export
  testGroupFailure : TestGroup n a -> Vect n Type
  testGroupFailure [] = []
  testGroupFailure (x :: xs) = testFailure x :: testGroupFailure xs

namespace testResult

  public export
  data TestGroupResult : Vect n Type -> Type where
    Nil  : TestGroupResult []
    (::) : Either t Nat -> TestGroupResult xs -> TestGroupResult (t :: xs)

  runGroup : (tg : TestGroup n a) -> a -> TestGroupResult (testGroupFailure tg)
  runGroup [] x = []
  runGroup (y :: xs) x = test y x :: runGroup xs x


namespace testMapping

  public export
  data TestMapping : Vect n Type -> Type -> Type where
    Nil  : TestMapping [] o
    (::) : (Either t Nat -> o)
        -> TestMapping xs o
        -> TestMapping (t :: xs) o

  mapResult : TestMapping tg o -> TestGroupResult tg -> List o
  mapResult [] [] = []
  mapResult (f :: fs) (x :: xs) = f x :: mapResult fs xs
