import Game.Levels.LoopWorld.L02_InventInvariant

open LeanModels LeanModels.Python

World "LoopWorld"
Level 3

Title "The sum of odd numbers"

Introduction "
Fresh program, no rehearsal:

```python
def odd_sum(n):
    total = 0
    k = 0
    while k < n:
        total = total + 2 * k + 1
        k = k + 1
    return total
```

`1 + 3 + 5 + ⋯` — the first `n` odd numbers. The claim: the answer is
exactly `n * n`. (Really: `1 + 3 = 4`, `1 + 3 + 5 = 9`, `1 + 3 + 5 + 7 = 16`
— squares, every time. Now *prove* it, for all `n` at once.)

You have the whole toolkit. Clause form or delayed form, your choice. To
invent the invariant, ask the standard questions:

* **The books.** After `k` laps, what is `total`? The first `k` odd numbers
  sum to… (that's the theorem itself, one loop iteration early).
* **The range.** What keeps `k` honest between entry and exit? You need
  enough to pin `k` at the exit: the test says `¬ k < n`, so the ceiling
  conjunct `k ≤ n` forces `k = n` there.
* **The measure.** What shrinks every lap, and never goes below zero?

This invariant is friendlier than `tri`'s — the books balance without any
`2 *` trick, and at the exit `k = n` turns `total = k * k` into the goal on
the spot, so `all_goals grind` can even sweep the `ret` goal unaided.
"

/-- `odd_sum(n) ==> n * n` for every `n ≥ 0`: the sum of the first `n` odd
numbers is `n²` — proved by a player-invented invariant. -/
TheoremDoc odd_sum_total as "odd_sum_total" in "Python programs"

/-- For every integer `n ≥ 0`, running `odd_sum` terminates and returns
`n * n`: the sum of the first `n` odd numbers is a perfect square. -/
Statement odd_sum_total (n : PyInt) (hn : 0 ≤ n) : odd_sum(n) ==> n * n := by
  Hint "Loop variables: `total` and `k` (both assigned in the body; `n`
  isn't). Invariant: `0 ≤ k ∧ k ≤ n ∧ total = k * k`. Measure:
  `(n - k).toNat`. Hand them over —
  `py_vcgen [odd_sum] (inv := fun (total k : Int) => 0 ≤ k ∧ k ≤ n ∧ total = k * k)
  (dec := fun (total k : Int) => (n - k).toNat)` — or go delayed and answer
  `inv1`/`dec1` with `exact`."
  py_vcgen [odd_sum]
    (inv := fun (total k : Int) => 0 ≤ k ∧ k ≤ n ∧ total = k * k)
    (dec := fun (total k : Int) => (n - k).toNat)
  Hint "All five residuals are `grind`-shaped this time — even the `ret`
  payout: from `¬ k' < n` and `k' ≤ n`, `grind` pins `k' = n` and rewrites
  `total' = k' * k'` into the goal. Sweep: `all_goals grind`."
  all_goals grind

Conclusion "
`1 + 3 + 5 + ⋯ + (2n−1) = n²` — you likely met this as a proof by induction.
You just watched what that induction *is operationally*: the invariant is
the induction hypothesis, `init` is the base case, `preserve` is the step,
and the exit cashes the hypothesis in at `k = n`.

So far every loop variable politely kept its name. Next level, Python
mutates its own argument — and your invariant needs a way to say
*“the value it started with”*.
"

NewDefinition odd_sum
