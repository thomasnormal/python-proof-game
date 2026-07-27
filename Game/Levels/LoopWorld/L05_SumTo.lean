import Game.Levels.LoopWorld.L04_OddSum

open LeanModels LeanModels.Python

World "LoopWorld"
Level 5

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

This loop counts **down** by mutating its own argument — a naming problem
your invariant has to survive.

Clause binders must be the Python names of the variables *assigned in the
loop body* — here `s` and `n`. So inside your clauses, `n` necessarily
means the **current, shrinking** value. But the theorem is about the value
`n` *started* as — and that name is already taken!

The escape is almost embarrassing: pick a different name in the *theorem*.
The statement binds the initial value as capital `N`; inside the clauses,
plain `n` is the current value and `N` the frozen initial one. Now the
invariant can say what's true mid-flight: the books — `s` already holds the
summed-off tail `(n+1) + ⋯ + N`, multiplication-free — plus the range, with
`n` itself (as a `Nat`) for the measure.

At the exit the test and the range floor pin the countdown at zero:
`obtain rfl : n' = 0 := by omega`, and the books collapse to the goal.
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
  Hint "Clause binders are the assigned Python names: `fun (s n : Int) => …`
  — and the frozen initial value is `N`, free for the invariant to mention."
  Hint (hidden := true) "`py_vcgen [sum_to]
  (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
  (dec := fun (s n : Int) => n.toNat)`"
  py_vcgen [sum_to]
    (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
    (dec := fun (s n : Int) => n.toNat)
  Hint (hidden := true) "Exit first: `case ret => obtain rfl : n' = 0 := by
  omega`, then `grind` for the division. The rest: `all_goals grind`."
  case ret =>
    obtain rfl : n' = 0 := by omega
    grind
  all_goals grind

Conclusion "
The shadowing rule in one line: **clause binders belong to the loop; the
theorem owns everything else** — when Python mutates its own argument,
rename at the theorem and keep the Python names for the clauses.

A new program, `steps`, is in your inventory. Read its source before the
next level: a branch has crept *inside* the loop body — and the claim will
need no hypothesis at all.
"

NewDefinition sum_to steps
