import Game.Levels.LoopWorld.L07_Gcd

open LeanModels LeanModels.Python

World "LoopWorld"
Level 8

Title "Cool-down: gcd doesn't care"

Introduction "
After Euclid, a breather — two lines, and the interpreter stays switched
off.

The program takes its arguments in order; the mathematics doesn't care:
`Int.gcd B A` is the same number as `Int.gcd A B`. So `gcd_total` — the
theorem you just bled for — should pay this out *without running anything*.

That's the whole point of a named theorem: prove once, spend forever.
`Int.gcd_comm` (new in your inventory) is the algebra; `py_corollary` is
the cashier; `gcd_total` is the account. One warning about the order of
business: **rewrite first, then collect** — `rw [Int.gcd_comm]` to turn the
goal into `gcd_total`'s exact shape, *then* `py_corollary [gcd_total]`.
(Handing both to `py_corollary` at once fails: it cannot reorient a
permutative rewrite underneath the spec's binders.)
"

/-- `gcd(A, B) ==> Int.gcd B A` for all `A, B ≥ 0` — the arguments'
order doesn't matter to the answer. A two-line corollary of `gcd_total`:
no interpreter, no invariant, just `Int.gcd_comm` and the theorem you
already own. -/
TheoremDoc gcd_comm as "gcd_comm" in "Python programs"

/-- For all integers `A, B ≥ 0`, running `gcd` returns `Int.gcd B A` too —
commutativity, cashed out of `gcd_total` without re-running the program. -/
Statement gcd_comm (A B : PyInt) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    gcd(A, B) ==> Int.gcd B A := by
  Hint "First make the goal's value look like `gcd_total`'s: rewrite
  `Int.gcd B A` into `Int.gcd A B` with the new commutativity lemma."
  Hint (hidden := true) "`rw [Int.gcd_comm]`."
  rw [Int.gcd_comm]
  Hint (hidden := true) "Now the goal *is* `gcd_total`'s statement:
  `py_corollary [gcd_total]` — the side conditions `hA`, `hB` are found by
  assumption."
  py_corollary [gcd_total]

Conclusion "
Two lines, zero interpreter. This is why theorems get names: `gcd_total`
just paid its first dividend, and it will keep paying.

Beyond the next door waits the boss's lair — `nested_flow`, freshly in your
inventory. Read its source before you knock.
"

NewTheorem Int.gcd_comm
NewDefinition nested_flow
