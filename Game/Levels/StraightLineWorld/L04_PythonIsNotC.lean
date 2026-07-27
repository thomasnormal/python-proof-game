import Game.Levels.StraightLineWorld.L03_FloorMeansFloor

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 4

Title "Python is not C"

Introduction "
Ask C what `-7 / 2` is and it answers `-3`: C truncates toward zero — as do
Java, Rust, and Go. Ask Python what `-7 // 2` is and it answers `-4`:
Python floors. Same digits, different languages, different integer.

Step 3 of the arc is the cash-out: prove the C answer **impossible**. The
goal is a negation —

`¬ (arith.floordiv(-7, 2) ==> -3)`

— and in Lean, `¬ P` *is* the implication `P → False`. So the proof opens
by **assuming** the C-flavored claim: the new tactic `intro h` moves it into
your context, leaving `False` to prove.

From there: `py_check` proves what the run *actually* returns, determinism
confronts `h` with that run — one call, two alleged values, so `-3 = -4` —
and the newcomer **`omega`**, core Lean's decision procedure for linear
integer arithmetic, refutes it. (Last level `omega` was the wrong tool; a
false equation of `Int` literals is its home turf, and there it never
misses.)

No compiler flag, no folklore: a machine-checked proof that two programming
languages disagree about one expression.
"

/-- `arith.floordiv(-7, 2)` cannot return `-3`, the answer C's truncating
division would give. The run returns `-4` (floor), and the interpreter is
deterministic — so the languages *provably* disagree. -/
TheoremDoc python_is_not_C as "python_is_not_C" in "Python programs"

/-- Running `floordiv` on `-7` and `2` does **not** return `-3` — C's
truncating answer. Python floors: the run returns `-4`, and determinism
makes any other value absurd. -/
Statement python_is_not_C : ¬ (arith.floordiv(-7, 2) ==> -3) := by
  Hint (strict := true) "A negation is an implication: `¬ P` unfolds to
  `P → False`. Assume the C answer: `intro h`."
  intro h
  Hint (strict := true) "Goal `False`, and `h` claims the run returns `-3`.
  Establish what it *really* returns:
  `have hrun : arith.floordiv(-7, 2) ==> -4 := by py_check`
  — a concrete run, so `py_check` executes it in-kernel."
  have hrun : arith.floordiv(-7, 2) ==> -4 := by py_check
  Hint (strict := true) (hidden := true) "One call, two alleged return
  values. Determinism collapses them:
  `have h34 := CallsTo.typed_int_eq h hrun` — read the type it infers:
  `h34 : -3 = -4`."
  have h34 := CallsTo.typed_int_eq h hrun
  Hint (strict := true) (hidden := true) "A false equation between integer
  literals, at honest `Int`. `omega` finishes."
  omega

Conclusion "
`-3 = -4` — absurd, C refuted, arc closed: **named** (`midpoint_spec`),
**proved** (`floordiv_is_floor`), **spent** (`python_is_not_C`).

The load-bearing ingredient was **determinism**: testing can show what a
run returned, never what a run *cannot* return. One observed run plus
`CallsTo.typed_int_eq` upgrades a data point into an impossibility theorem.

Back to the regular program: cashing proved runs into prettier statements.
"

NewTactic intro omega
