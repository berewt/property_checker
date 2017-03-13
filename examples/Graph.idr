module GraphExample

import Data.SortedMap as M
import Data.Fun
import Data.HVect

import PropertyChecker

public export
Edge : Type
Edge = (Nat, Nat)

public export
DirectedGraph : Type -> Type
DirectedGraph a = SortedMap Edge a

swapKey : (Edge, a) -> (Edge, a)
swapKey (k, v) = (swap k, v)


invertGraph : DirectedGraph a -> DirectedGraph a
invertGraph = fromList . map (\(k, v) => (swap k, v)) . toList

fromOriginalToInverted : Eq a => Test (DirectedGraph a)
fromOriginalToInverted
  = MkTest [forall M.toList, exists (M.toList . invertGraph)]
           (\x, y => swapKey x == y)

fromInvertedToOriginal : Eq a => Test (DirectedGraph a)
fromInvertedToOriginal
  = MkTest [forall (M.toList . invertGraph), exists M.toList]
           (\x, y => swapKey x == y)

invertedElementsNumber : Test (DirectedGraph a)
invertedElementsNumber
  = MkTest [forall (pure . M.toList), forall (pure . M.toList . invertGraph)]
           (\x, y => length x == length y)

checkInversion : Eq a => TestGroup 3 (DirectedGraph a)
checkInversion = [ fromOriginalToInverted
                 , fromInvertedToOriginal
                 , invertedElementsNumber
                 ]

checkInversionExample : TestGroupResult (testGroupFailure (checkInversion {a = String}))
checkInversionExample =
  let gr = [((1,2), "foo"), ((1,3), "bar"), ((2,3), "foobar")]
  in  runGroup checkInversion (M.fromList gr)


record InvertedGraph a where
  constructor MkInveredGraph
  getInvertedGraph : DirectedGraph a


{-
fromOriginalToInverted' : Eq a => Test (DirectedGraph a)
fromOriginalToInverted'
  = MkTest [ All (fromContext M.toList . get)
           , Any (fromContext $ M.toList . getInvertGraph)
           ]
           (\x, y => swapKey x == y)

fromInvertedToOriginal : Eq a => Test (DirectedGraph a)
fromInvertedToOriginal
  = MkTest [ All (fromContext $ M.toList . invertGraph)
           , Any (fromContext M.toList)
           ]
           (\x, y => swapKey x == y)

invertedElementsNumber : Test (DirectedGraph a)
invertedElementsNumber
  = MkTest [ All (fromContext (the (List _) . pure . M.toList))
           , All (fromContext (the (List _) . pure . M.toList . invertGraph))
           ]
           (\x, y => length x == length y)

checkInversion : Eq a => TestGroup 3 (DirectedGraph a)
checkInversion = [ fromOriginalToInverted
                 , fromInvertedToOriginal
                 , invertedElementsNumber
                 ]
-}
