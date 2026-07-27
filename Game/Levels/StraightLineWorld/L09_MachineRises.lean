import Game.Levels.StraightLineWorld.L08_Clamp01Boss

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 9

Title "The machine rises"

Introduction "
Look at your boss proof again: commit fuel, split the branches, execute each
one symbolically, finish the arithmetic. Every move was *mechanical* — you
just had to make them in the right order, through shapes `py_prove`'s recipe
couldn't handle.

Mechanical moves in the right order is what machines are for. Meet
**`py_vcgen`**, the framework's verification-condition walker: it takes the
function body and *walks* it — straight-line pieces discharged by symbolic
execution, each `if` forking the walk with its test recorded as a fact —
and whatever mathematics is left over, it hands back to you as tagged goals.

Same machine, same two sequential `if`s — but this time the claim is nested
the *other* way: `min 1 (max 0 x)`. By hand, that would be all four cases
again from scratch. Instead: one `py_vcgen [ag_clamp01]` call, and then sweep
the three leftover return goals with `all_goals omega` (`all_goals tac` runs
`tac` on every remaining goal).

Everything you just did by hand — generated.
"

/-- `ag_clamp01.clamp01(x) ==> min 1 (max 0 x)` — the boss statement with the
`min`/`max` nested the other way, proved by the VC walker: `py_vcgen`
generates the case analysis you performed manually one level ago. -/
TheoremDoc clamp01_machine as "clamp01_machine" in "Python programs"

/-- For every integer `x`, running `clamp01` terminates and returns
`min 1 (max 0 x)` — the same clamped value, nested the other way. This time
the machine does the walking. -/
Statement clamp01_machine (x : PyInt) : ag_clamp01.clamp01(x) ==> min 1 (max 0 x) := by
  Hint "Unleash it: `py_vcgen [ag_clamp01]`."
  py_vcgen [ag_clamp01]
  Hint "Three goals, one per `return` — tagged `ret`, `ret2`, `ret3` (goals
  that would share a tag get numbered) — each bare integer arithmetic, the
  branch facts sitting in your hypotheses as `hif`. No fuel, no interpreter,
  no `Val` anywhere: the machine already ate all of that. Sweep them."
  Hint (hidden := true) "`all_goals omega`."
  all_goals omega

Conclusion "
That was the entire boss fight, mechanized — and the arithmetic leftovers are
*honest* leftovers: no tactic can know that `0` is the right answer below `0`.
That's mathematics about the program, and it's yours.

Notice what `py_vcgen` did **not** need: fuel. It never runs the whole
program — it walks the code and splices captured symbolic runs together. Why
does that matter? Because up to now, every proof secretly ended with “…and
the run finishes in some number of steps we exhibited.” For a `while` loop
over a symbolic input, *no fixed number of steps suffices* — and that is
exactly where walking beats running.

**Loop World** is open. Bring an invariant.
"

NewTactic py_vcgen all_goals
