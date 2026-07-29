import Game.Levels.LoopWorld.L01_ReadTheProof

open LeanModels LeanModels.Python

World "LoopWorld"
Level 2

Title "Invent the invariant"

Introduction "
Same theorem. Empty editor. Your invariant.

Call the walker **bare** — `py_vcgen [tri]`, no clauses. It walks as far
as it can, then hands *you* the pen: `case inv1` asks for the invariant,
`case dec1` for the measure — each goal hands you the loop's variables by
name in the context (`total i : Int`), so you answer with a **bare
proposition** over them: `exact 0 ≤ i ∧ …` — not a lambda, not a proof, a
**definition**, and the residuals are the referee.

Two classic wrong guesses, so you'll recognize their shapes forever:

* **Too weak** — the books alone, `2 * total = i * (i - 1)`, no range
  conjuncts. Everything before the exit sails through, but `ret` is left
  holding `hcont : n < i'` and nothing else — the exit could be any
  `i' > n`, so the claim doesn't follow; `grind` fails, its diagnostics
  even sketching a countermodel. An invariant can be *true* and still
  *useless*: it must cash out at the exit. Add the range:
  `0 ≤ i ∧ i ≤ n + 1`.
* **Wrong measure** — `i.toNat` sounds plausible, but `i` *grows*: the
  `dec` goal comes back reading `(i + 1).toNat < i.toNat`, visibly false.
  The measure is the distance *remaining*, not traveled:
  `(n + 1 - i).toNat`.

You know the answer. This time, *you* type it.
"

/-- For every integer `n ≥ 0`, running `tri` terminates and returns
`n * (n + 1) / 2` — same claim as last level, but this time the invariant is
yours: `py_vcgen [tri]` bare, then answer `inv1` and `dec1`. -/
Statement (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  Hint "Call the walker with no clauses: `py_vcgen [tri]`."
  py_vcgen [tri]
  Hint "The walker wants the invariant first: `case inv1` hands you `total i
  : Int` in the goal context — answer with a bare proposition: range floor,
  range ceiling, and the books. If you commit a weaker guess, the residuals
  will tell on you."
  Hint (hidden := true) "`case inv1 => exact 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)`"
  case inv1 => exact 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)
  Hint (hidden := true) "Now the measure — the distance still to travel, as
  a `Nat`: `case dec1 => exact (n + 1 - i).toNat`

  (If you try `i.toNat` instead, the `dec` goal will come back visibly
  hopeless. Distance *remaining*, not distance traveled.)"
  case dec1 => exact (n + 1 - i).toNat
  Hint (hidden := true) "Committed — the residuals are now instantiated.
  Finish exactly as you read last level: `case ret => obtain rfl : i' = n + 1
  := by omega` then `grind`, and sweep the rest with `all_goals grind`."
  case ret =>
    obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind

Conclusion "
That was the real thing. Nobody — human or machine — *derives* an
invariant; you guess one, and the residuals referee the guess. The tags
always tell you which way to adjust.

(House-style footnote: the books are stated multiplication-free — `2 *
total = …` — to keep integer division out of the algebra; the habit pays
off on later programs even where `grind` could survive the pretty form.)

Two fresh programs just landed in your inventory: `double_sum` and
`odd_sum`. No rehearsals from here on.
"

NewTactic exact
NewDefinition double_sum odd_sum
