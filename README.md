# Property checker

The idea is to express and check properties (and in a future version, to obtain an error summary if some properties don't hold).

## Example

Check that ∀ x ∈ {2,4,6}. ∃ y ∈ {3,8,5,7}. x + y = 9:

```idris
testExample : Bool -- True
testExample = test_ [forall [2,4,6], exists [3,5,7,8]] (\x, y => (x + y == 9))
```

Yeah, I know, I should take time to add more complex examples.
