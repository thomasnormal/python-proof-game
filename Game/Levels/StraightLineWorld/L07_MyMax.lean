import Game.Levels.StraightLineWorld.L06_MyAbs

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 7

Title "Fork, again"

Introduction "
The second fork in your deck:

```python
def my_max(a: int, b: int) -> int:
    if a < b:
        return b
    return a
```

Two variables this time, and a test that compares them *to each other*.
Before you fire anything, trace one case in your head: when `a = b`, which
branch runs — and does the value it returns agree with the goal's
`max a b` there?

One lone `if`. You know whose territory that is.
"

/-- For all integers `a` and `b`, running `my_max` terminates and returns
`max a b`. -/
Statement (a b : PyInt) : my_max(a, b) ==> max a b := by
  Hint "Same recipe as `my_abs`: a single surviving `if` splits, and the
  finisher knows `max` as natively as it knew `|·|`."
  Hint (hidden := true) "`py_prove [my_max]`."
  py_prove [my_max]

Conclusion "
Note the case you traced: at `a = b` the test fails, the program returns
`a` — and `max a b` *is* `a` there. The proof covered the boundary because
the boundary is just another integer.

Next door: the boss. It has been warned about you.
"
