# Property checker

The idea is to express and check properties. If the property does not held, the library should provide a precise output of the values that makes the property failed.

## Examples

## Valid example

Check that ∀ x ∈ {2,4,6}. ∃ y ∈ {3,8,5,7}. x + y = 9:

```idris
testExample : Bool
testExample = test_ $ MkTest [allFrom [2,4,6], anyFrom [3,5,7,8]] (\x, y => (x + y == 9))
```

Output:

```
Right 3 : Either (Failure [AllMarker Integer, AnyMarker Integer]) Nat
```

In that case, the output corresponds to the number of tests that succeed.

### Invalid example

Check that ∀ x ∈ {2,4,6}. ∃ y ∈ {3,8,5,7}. x + y = 9:

```idris
testExample : Bool
testExample = test_ $ MkTest [allFrom [2,4,6], anyFrom [3,8,10]] (\x, y => (x + y == 9))
```

Output:

```
Left (AllFailure [(2,
                   AnyFailure [(3, EmptyFailure),
                               (8, EmptyFailure),
                               (10, EmptyFailure)]),
                  (4,
                   AnyFailure [(3, EmptyFailure),
                               (8, EmptyFailure),
                               (10,
                                EmptyFailure)])]) : Either (Failure [AllMarker Integer,
                                                                     AnyMarker Integer])
                                                           Nat
```

Which can be read as two errors:

- 2 in the 1st selection (none of 3, 8 or 10 in the second selection fits)
- 4 in the 1st selection (none of 3, 8 or 10 in the second selection fits)


## More examples

See the [examples](examples) directory.
