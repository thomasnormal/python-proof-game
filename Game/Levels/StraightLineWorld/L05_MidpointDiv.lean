import Game.Levels.StraightLineWorld.L04_PythonIsNotC

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 5

Title "The strongest honest statement"

Introduction "
Clients of `midpoint` don't want to read `Int.fdiv`. They want the pretty
form `(a + b) / 2`, in Lean's own `/`. Is that even true? Lean's `/` on
`Int` is *Euclidean* division — a third convention for your zoo — but for a
**positive divisor**, Euclidean and floor division agree exactly, and the
divisor here is the literal `2`. So the pretty form holds for *every* `a`
and `b`. No fine print.

Which settles what the theorem must say. You might be tempted to guard it —
`0 ≤ a`, `0 ≤ b`, “midpoints of nonnegative things” — but a hypothesis the
proof never uses is dead weight in the statement's teeth: it weakens the
theorem and documents a dependency that does not exist. The house rule has
two halves: **preconditions are ordinary hypotheses** — no special contract
language, they sit to the left of the turnstile like any other fact — and
**you state exactly the load-bearing ones**. You've already leaned on a real
one: `0 < b` in “Floor means floor” fed the division algorithm. Loop World's
first theorem will genuinely need `0 ≤ n`. Here, the honest statement takes
none.

Now, how to prove it? You could re-run the program symbolically… but you
already own `midpoint_spec` (check your inventory!). It pins the returned
value to `Int.fdiv (a + b) 2`; the only new content is *arithmetic*:
`Int.fdiv (a + b) 2 = (a + b) / 2` — which is exactly the library lemma
`Int.fdiv_eq_ediv_of_nonneg`, at divisor `2`.

`py_corollary [thm, rewrites…]` packages this move: derive a corollary of a
proved run-theorem by *rewriting its value*, never re-executing the program.
"

/-- `midpoint(a, b) ==> (a + b) / 2` for **all** integers — the pretty
corollary of `midpoint_spec`, derived by value rewriting, not re-execution.
Unconditional, because Lean's `/` (Euclidean division) agrees with floor
division whenever the divisor is positive — and the divisor is `2`. -/
TheoremDoc midpoint_div as "midpoint_div" in "Python programs"

/-- For every `a` and `b`, `midpoint` terminates and returns `(a + b) / 2` —
the pretty `/` form, earned from `midpoint_spec` plus arithmetic, without
re-running the program. -/
Statement midpoint_div (a b : PyInt) : midpoint(a, b) ==> (a + b) / 2 := by
  Hint "Don't re-execute anything. Bridge the value of `midpoint_spec` to the
  `/` form: `py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]`."
  py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]

Conclusion "
One proof ran the program; every corollary after it is pure mathematics.

And note which way the honesty cut: *dropping* the tempting `0 ≤ a`, `0 ≤ b`
guards made the theorem stronger — the pretty form covers
`midpoint(3, -4) ==> -1` too, the very run that tripped you in Machine
World. The agreement is genuinely conditional only when the **divisor** goes
symbolic — `Int.fdiv_eq_ediv_of_nonneg` demands `0 ≤ b` for a reason — and
the day a hypothesis is load-bearing, it goes back in. Specs are promises to
readers: promise exactly what is true, under exactly the assumptions it
needs.
"

NewTheorem Int.fdiv_eq_ediv_of_nonneg
NewTactic py_corollary
