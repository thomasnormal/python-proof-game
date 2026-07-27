import Game.Levels.StraightLineWorld

open LeanModels LeanModels.Python

World "LoopWorld"
Level 1

Title "Anatomy of a loop proof"

Introduction "
Old friend, new claim. `tri` — the very first program you ever ran — and this
time the input is **symbolic**: for every `n ≥ 0`, `tri(n)` returns the
triangular number `n * (n + 1) / 2`.

```python
def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total
```

No case split can cover a `while` loop: the number of iterations depends on
`n`. What covers it is an idea from 1969 — the **loop invariant**: a fact
that holds when the loop starts and survives every iteration, so it still
holds when the loop ends, *however many* iterations that took. Plus a
**decreasing measure**: a natural number that strictly drops each iteration,
so the loop cannot run forever. These two are the content no machine can
invent; everything else is walking, and walking is `py_vcgen`'s job.

You hand them over as clauses. This once, they're already written in the
editor — **read** them before you run them:

* `inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)`
  — the binders `total`, `i` are the Python variables the loop assigns; `n`
  isn't assigned, so the invariant mentions it directly. The three conjuncts:
  a range floor, a range ceiling, and *the books*: `total` holds
  `0 + 1 + ⋯ + (i-1)`, stated multiplication-free as `2·total = i·(i-1)`.
* `dec := fun (total i : Int) => (n + 1 - i).toNat` — the distance still to
  travel, as a natural number.

`py_vcgen` opens the loop with them and leaves six *residual* goals, each
tagged with its role — this is the shape of every loop proof you'll ever do:

* **`init`** — the invariant holds on entry (`total = 0`, `i = 0`).
* **`preserve`** and **`preserve2`** — one body pass keeps the invariant
  (the test fact `hcont : i ≤ n` is in scope — the body only runs when the
  test passed). Preservation splits along the invariant's conjuncts; the
  walker closes what it can on the spot and leaves two — the range floor
  and the books. When goals share a tag, the walker numbers them: the first
  keeps the bare tag, the second becomes `preserve2`, so each has its own
  `case` address.
* **`dec`** — the measure strictly drops on that same pass.
* **`exit`** — bookkeeping: repackage the invariant and the negated test at
  the moment the loop ends (a goal full of `∃`s; `grind` eats it whole).
* **`ret`** — the payout: primed variables `total'`, `i'` are the values *at
  the exit*, and the invariant plus `hcont : n < i'` must force the returned
  value. This one is handled first below: the range conjuncts and the negated
  test pin `i' = n + 1` (`obtain rfl : i' = n + 1 := by omega` proves that
  equation and substitutes it everywhere), and the remaining division algebra
  falls to `grind`.

Your job this level: fill the two holes — both are one word, and the word is
`grind`.
"

/-- `tri(n) ==> n * (n + 1) / 2` for every `n ≥ 0` — the game's first loop
theorem: one invariant and one measure cover *every* number of iterations at
once. -/
TheoremDoc tri_total as "tri_total" in "Python programs"

/-- For every integer `n ≥ 0`, running `tri` terminates and returns the
triangular number `n * (n + 1) / 2` — infinitely many loop iterations
covered by one invariant. -/
Statement tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  Template
    py_vcgen [tri]
      (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
      (dec := fun (total i : Int) => (n + 1 - i).toNat)
    case ret =>
      obtain rfl : i' = n + 1 := by omega
      Hole grind
    all_goals Hole grind

Conclusion "
Read the goals you just watched close, once more, in prose: *it holds at the
door, every lap keeps it, every lap shortens the road, and at the exit it
pays out.* That's the whole theory of `while`.

The invariant was given to you this time. Next level, the training wheels
come off — mid-proof.
"

NewTactic case obtain rfl
NewHiddenTactic Hole
NewTheorem rfl
NewDefinition Int
