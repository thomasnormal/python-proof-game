import Game.Levels.LoopWorld.L01_ReadTheProof

open LeanModels LeanModels.Python

World "LoopWorld"
Level 2

Title "Invent the invariant"

Introduction "
Same theorem. Empty editor. Your invariant.

Here's the move: call the walker **bare** — `py_vcgen [tri]`, no clauses.
It walks as far as it can, then stops and hands *you* the pen. The first two
goals are requests, not facts:

* `case inv1 ⊢ Int → Int → Prop` — “give me the invariant” (a predicate on
  the assigned variables `total` and `i`), and
* `case dec1 ⊢ Int → Int → Nat` — “give me the measure”.

Every goal after them shows your unknowns as `?inv1` and `?dec1` — the
residuals are waiting to be *instantiated by your guess*. Answer with
`exact`: `case inv1 => exact fun total i => …`. You're not proving anything
yet; you're **defining** something, and the moment you commit, every
downstream goal is rewritten with your definition. The residuals are the
referee. That's the actual experience of verification, and this level is it.

Two classic wrong guesses, so you recognize the failure shapes when you meet
them (and you will, for the rest of your life):

* **Too weak** — the books alone, `2 * total = i * (i - 1)`, no range
  conjuncts. Everything *before* the exit sails through: the equation really
  does survive every lap. But the `ret` goal is left holding
  `hcont : n < i'` and nothing else — the exit could be any `i' > n`, and
  `total' = n * (n + 1) / 2` simply doesn't follow. `grind` fails, and its
  diagnostics even sketch a countermodel. An invariant can be *true* and
  still *useless*: it must be strong enough to cash out at the exit. Add the
  range: `0 ≤ i ∧ i ≤ n + 1`.
* **Wrong measure** — `i.toNat` sounds plausible (“it's the loop counter!”),
  but `i` *grows*. The `dec` goal comes back reading
  `(i + 1).toNat < i.toNat` — visibly false, no prover needed. The measure
  is the distance *remaining*, not the distance traveled: `(n + 1 - i).toNat`.

You know the right answer from last level. This time, *you* type it.
"

/-- For every integer `n ≥ 0`, running `tri` terminates and returns
`n * (n + 1) / 2` — same claim as last level, but this time the invariant is
yours: `py_vcgen [tri]` bare, then answer `inv1` and `dec1`. -/
Statement (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  Hint "Call the walker with no clauses: `py_vcgen [tri]`."
  py_vcgen [tri]
  Hint "The walker wants the invariant first:
  `case inv1 => exact fun total i => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)`

  (Range floor, range ceiling, and the books. If you commit a weaker guess,
  the residuals will tell on you — everything closes except `ret`.)"
  case inv1 => exact fun total i => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)
  Hint "Now the measure — the distance still to travel, as a `Nat`:
  `case dec1 => exact fun total i => (n + 1 - i).toNat`

  (If you try `i.toNat` instead, the `dec` goal will come back reading
  `(i + 1).toNat < i.toNat` — visibly hopeless. Distance *remaining*, not
  distance traveled.)"
  case dec1 => exact fun total i => (n + 1 - i).toNat
  Hint "Committed. The residuals are now instantiated with your invariant —
  finish exactly as you read last level: `case ret => obtain rfl : i' = n + 1
  := by omega` then `grind`, and sweep the rest with `all_goals grind`."
  case ret =>
    obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind

Conclusion "
That was the real thing. Nobody — human or machine — *derives* an invariant;
you guess one, and the residual goals referee the guess. Too weak and the
exit won't pay out; wrong measure and `dec` shows you a plainly false
inequality. The tags always tell you which way to adjust.

(House-style footnote: we state the books multiplication-free —
`2 * total = i * (i - 1)` rather than `total = i * (i - 1) / 2` — to keep
integer division out of the algebra. Here `grind`'s division theory would
actually survive the pretty form; on later programs it won't, and the
`2 *` habit is what you'll want in your hands.)

Next: a program you've never proved anything about, and no rehearsal.
"

NewTactic exact
