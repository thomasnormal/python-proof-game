import Game.Levels.StraightLineWorld.L02_MidpointSpec

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 3

Title "Preconditions are hypotheses"

Introduction "
Clients of `midpoint` don't want to read `Int.fdiv`. They want the pretty
form `(a + b) / 2` — and they're entitled to it *when it's true*: floor
division and Lean's `/` agree once the operands behave, and here the goal
hands you `ha : 0 ≤ a` and `hb : 0 ≤ b`.

That's the whole convention for preconditions in this framework: **they are
ordinary hypotheses**. No special contract language — `0 ≤ a` sits to the
left of the turnstile like any other fact.

Now, how to prove it? You could re-run the program symbolically… but you
already own `midpoint_spec` (check your inventory!). It pins the returned
value to `Int.fdiv (a + b) 2`; the only new content is *arithmetic*:
`Int.fdiv (a + b) 2 = (a + b) / 2` under the sign hypotheses — which is
exactly the library lemma `Int.fdiv_eq_ediv_of_nonneg`.

`py_corollary [thm, rewrites…]` packages this move: derive a corollary of a
proved run-theorem by *rewriting its value*, never re-executing the program.
"

/-- `midpoint(a, b) ==> (a + b) / 2` under `0 ≤ a`, `0 ≤ b` — the pretty
corollary of `midpoint_spec`, derived by value rewriting, not re-execution. -/
TheoremDoc midpoint_nonneg as "midpoint_nonneg" in "Python programs"

/-- For nonnegative `a` and `b`, `midpoint` terminates and returns
`(a + b) / 2` — the pretty `/` form, earned from `midpoint_spec` plus
arithmetic, without re-running the program. -/
Statement midpoint_nonneg (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    midpoint(a, b) ==> (a + b) / 2 := by
  Hint "Don't re-execute anything. Bridge the value of `midpoint_spec` to the
  `/` form: `py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]`."
  py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]

Conclusion "
One proof ran the program; every corollary after it is pure mathematics.

Full-disclosure footnote, in the spirit of this framework: on this toolchain
`/` on `Int` is *Euclidean* division, which already agrees with floor division
for any **positive divisor** — so `ha` and `hb` aren't load-bearing for
divisor `2`. The statement keeps them because it's the honest, portable
contract for the pretty form. Specs are promises to readers, not just to the
kernel.
"

NewTheorem Int.fdiv_eq_ediv_of_nonneg
NewTactic py_corollary
