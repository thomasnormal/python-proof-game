import Game.Levels.StraightLineWorld.L01_AddTotal

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 2

Title "Say floor when you mean floor"

Introduction "
Back to our one-liner, now with symbolic inputs:

```python
def midpoint(a: int, b: int) -> int:
    return (a + b) // 2
```

What does `midpoint` return *in general*? “`(a + b) / 2`, obviously” — but
Machine World already caught you once: `midpoint(3, -4)` is `-1`, not `0`.
Python's `//` **floors**.

Lean has a whole zoo of integer divisions: `Int.div` truncates toward zero,
`/` is Euclidean division, and `Int.fdiv` floors. Only one of them is what
`//` means, and the goal says it out loud: `Int.fdiv (a + b) 2`.

This is the framework's honesty policy: the divergence between `//` and “the
division you assumed” belongs **in the statement**, never buried in a
translation.

The body is one line — `py_prove` territory.
"

/-- `midpoint(a, b) ==> Int.fdiv (a + b) 2` for all integers — *floor*
division, which is what Python's `//` means. The next level derives its
pretty `/` corollary via `py_corollary`. -/
TheoremDoc midpoint_spec as "midpoint_spec" in "Python programs"

/-- For all integers `a` and `b`, running `midpoint` terminates and returns
`Int.fdiv (a + b) 2` — **floor** division, the honest reading of `//`. -/
Statement midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2 := by
  Hint "One straight-line body, one call: `py_prove [midpoint]`. Internally,
  `py_simp` reduces the interpreter's `//` operation to `Int.fdiv` and
  discharges the `2 = 0` divisor guard on the way."
  py_prove [midpoint]

Conclusion "
Proved — and *named*. `midpoint_spec` is now in your inventory, and the next
level shows why that matters: good theorems get reused, not re-proved.
"

NewDefinition Int.fdiv
