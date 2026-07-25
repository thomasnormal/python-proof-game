import Game.Levels.LoopWorld.L03_OddSum

open LeanModels LeanModels.Python

World "LoopWorld"
Level 4

Title "The shadowed variable"

Introduction "
Triangular numbers again — but read the body carefully:

```python
def sum_to(n: int) -> int:
    s = 0
    while n > 0:
        s += n
        n -= 1
    return s
```

This loop counts **down**, and it does so by mutating its own argument:
`n -= 1`. That creates a naming problem your invariant has to survive.

Clause binders must be the Python names of the variables *assigned in the
loop body* — here `s` and `n`. So inside your clauses, `n` necessarily means
the **current, shrinking** value. But the theorem is about the value `n`
*started* as — and that name is already taken!

The escape is almost embarrassing: pick a different name in the *theorem*.
The statement binds the initial value as capital `N`, so inside the clauses,
plain `n` is the loop's current value and `N` is the frozen initial one. The
goal reads `sum_to(N) ==> N * (N + 1) / 2`, and the invariant can finally
say what's true mid-flight:

* the books: `s` already holds the summed-off tail `(n+1) + (n+2) + ⋯ + N`,
  multiplication-free: `2 * s = (N - n) * (N + n + 1)`;
* the range: `0 ≤ n ∧ n ≤ N`;
* the measure: `n` itself is the distance left — `n.toNat`.

At the exit the test gives `¬ n' > 0`, the range floor gives `0 ≤ n'`, so
`obtain rfl : n' = 0 := by omega` pins the countdown at zero and the books
collapse to the goal.
"

/-- `sum_to(N) ==> N * (N + 1) / 2` for every `N ≥ 0` — the countdown
triangular sum. The Python variable `n` is mutated by the loop, so the
theorem binds the *initial* value under the fresh name `N`, leaving the name
`n` free to mean the current value inside the clauses. -/
TheoremDoc sum_to_total as "sum_to_total" in "Python programs"

/-- For every integer `N ≥ 0`, running `sum_to` terminates and returns
`N * (N + 1) / 2`. Capital `N` is the *initial* value of the Python variable
`n` — the loop mutates `n` itself. -/
Statement sum_to_total (N : PyInt) (hN : 0 ≤ N) : sum_to(N) ==> N * (N + 1) / 2 := by
  Hint "Clause binders are the assigned Python names: `fun (s n : Int) => …`.
  Invariant: `0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1)`. Measure:
  `n.toNat`. So:
  `py_vcgen [sum_to] (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
  (dec := fun (s n : Int) => n.toNat)`."
  py_vcgen [sum_to]
    (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
    (dec := fun (s n : Int) => n.toNat)
  Hint "Exit first: `case ret => obtain rfl : n' = 0 := by omega`, then
  `grind` for the division. The rest: `all_goals grind`."
  case ret =>
    obtain rfl : n' = 0 := by omega
    grind
  all_goals grind

Conclusion "
The shadowing rule in one line: **clause binders belong to the loop; the
theorem owns everything else** — so when Python mutates its own argument,
rename at the theorem and keep the Python names for the clauses. (This is
exactly how the lean-surfaces gallery states this theorem, for exactly this
reason.)

Next: the oldest algorithm in the book, and an invariant that isn't
bookkeeping — it's a *theorem about numbers*.
"

NewDefinition sum_to
