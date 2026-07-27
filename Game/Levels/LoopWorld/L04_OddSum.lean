import Game.Levels.LoopWorld.L03_DoubleSum

open LeanModels LeanModels.Python

World "LoopWorld"
Level 4

Title "The sum of odd numbers"

Introduction "
One number different, one theorem prettier:

```python
def odd_sum(n):
    total = 0
    k = 0
    while k < n:
        total = total + 2 * k + 1
        k = k + 1
    return total
```

`1 + 3 + 5 + ⋯` — the first `n` **odd** numbers. The claim: exactly
`n * n`. (`1 + 3 = 4`, `1 + 3 + 5 = 9`, `1 + 3 + 5 + 7 = 16` — squares,
every time. Now *prove* it, for all `n` at once.)

You have the whole toolkit and the questions are the standard three:

* **The books.** After `k` laps, what is `total`? (The theorem itself, one
  iteration early.)
* **The range.** The test says `¬ k < n` at the exit — which ceiling
  conjunct forces `k = n` there?
* **The measure.** What shrinks every lap, and never goes below zero?

Clause form or delayed form, your choice.
"

/-- `odd_sum(n) ==> n * n` for every `n ≥ 0`: the sum of the first `n` odd
numbers is `n²` — proved by a player-invented invariant. -/
TheoremDoc odd_sum_total as "odd_sum_total" in "Python programs"

/-- For every integer `n ≥ 0`, running `odd_sum` terminates and returns
`n * n`: the sum of the first `n` odd numbers is a perfect square. -/
Statement odd_sum_total (n : PyInt) (hn : 0 ≤ n) : odd_sum(n) ==> n * n := by
  Hint "Loop variables: `total` and `k` (both assigned in the body; `n`
  isn't). Answer the three questions, hand the clauses over — or go delayed
  and answer `inv1`/`dec1` with `exact`."
  Hint (hidden := true) "`py_vcgen [odd_sum]
  (inv := fun (total k : Int) => 0 ≤ k ∧ k ≤ n ∧ total = k * k)
  (dec := fun (total k : Int) => (n - k).toNat)`"
  py_vcgen [odd_sum]
    (inv := fun (total k : Int) => 0 ≤ k ∧ k ≤ n ∧ total = k * k)
    (dec := fun (total k : Int) => (n - k).toNat)
  Hint (hidden := true) "All the residuals are `grind`-shaped — even the
  `ret` payout: from `¬ k' < n` and `k' ≤ n`, `grind` pins `k' = n` and
  rewrites the books into the goal. Sweep: `all_goals grind`."
  all_goals grind

Conclusion "
`1 + 3 + 5 + ⋯ + (2n−1) = n²` — you likely met this as a proof by
induction. You just watched what that induction *is operationally*: the
invariant is the hypothesis, `init` the base case, `preserve` the step, and
the exit cashes in at `k = n`.

So far every loop variable politely kept its name. Next, Python mutates its
own argument.
"
