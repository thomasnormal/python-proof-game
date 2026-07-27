import Game.Levels.LoopWorld.L05_SumTo

open LeanModels LeanModels.Python

World "LoopWorld"
Level 6

Title "The walk home"

Introduction "
A loop with a **branch in its body**:

```python
def steps(n):
    count = 0
    while n != 0:
        if 0 < n:
            n = n - 1
        else:
            n = n + 1
        count = count + 1
    return count
```

Whatever side of zero `n` starts on, it walks home one step at a time —
Python computes an absolute value without ever writing `abs`. The claim is
`|N|`, and for the first time in this world it carries **no hypothesis**:
every integer walks home.

Everything here is a rerun. The argument is mutated, so the theorem binds
capital `N` (the `sum_to` move). The branch costs nothing: the walker forks
the body and carries each branch's fact into its residuals. Two questions:
what do `count` and `|n|` always add up to — and which *natural number*
shrinks on **both** branches? (`n.toNat` dies on the negative side; `|·|`
has a `Nat`-valued cousin, `n.natAbs`.)
"

/-- For **every** integer `N` — no hypothesis — running `steps` terminates
and returns `|N|`: the number of unit steps home. -/
Statement (N : PyInt) : steps(N) ==> |N| := by
  Hint "Clause binders, in body order: `fun (count n : Int) => …`. The
  invariant answers “what do `count` and `|n|` add up to?”; the measure is
  the `Nat`-valued distance from home."
  Hint (hidden := true) "`py_vcgen [steps]
  (inv := fun (count n : Int) => 0 ≤ count ∧ count + |n| = |N|)
  (dec := fun (count n : Int) => n.natAbs)`"
  py_vcgen [steps]
    (inv := fun (count n : Int) => 0 ≤ count ∧ count + |n| = |N|)
    (dec := fun (count n : Int) => n.natAbs)
  Hint (hidden := true) "Both branches leave the same shape of residual —
  one with `hif : 0 < n`, one with its negation — and every one is
  `grind`-food: `all_goals grind`."
  all_goals grind

Conclusion "
The branch never entered the invariant: `count + |n| = |N|` is true on
*both* sides, which is exactly why it survived. And no precondition — your
first loop theorem covering every integer input.

Next: the oldest algorithm in the book, and an invariant that isn't
bookkeeping — it's a *theorem about numbers*.
"
