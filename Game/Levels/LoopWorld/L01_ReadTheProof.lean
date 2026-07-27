import Game.Levels.StraightLineWorld

open LeanModels LeanModels.Python

World "LoopWorld"
Level 1

Title "Anatomy of a loop proof"

Introduction "
Old friend, new claim: for every `n ≥ 0`, `tri` — the first program you
ever ran — returns `n * (n + 1) / 2`.

No case split covers a `while` loop: the iteration count depends on `n`.
What covers it is an idea from 1969: the **loop invariant** — a fact every
lap preserves, so it survives to the exit however many laps run — plus a
**decreasing measure** — a natural number every lap shrinks, so the loop
cannot run forever. These two are the content no machine can invent; the
walking is `py_vcgen`'s job.

You hand them over as clauses, written in the editor this once: **read**,
then run. The binders `total`, `i` are the Python variables the loop
assigns; the conjuncts are a range floor, a range ceiling, and *the books*:
`total` holds `0 + 1 + ⋯ + (i-1)`, multiplication-free as
`2·total = i·(i-1)`.

The walker leaves six *residual* goals tagged by role — `init`, `preserve`,
`dec`, `exit`, `ret` — the shape of every loop proof from here on; the tag
glossary lives on the `py_vcgen` inventory tile. Keep it open.

Your job: fill the two holes — each is the single word `grind`.
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
