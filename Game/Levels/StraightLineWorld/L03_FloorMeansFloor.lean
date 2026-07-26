import Game.Levels.StraightLineWorld.L02_MidpointSpec

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 3

Title "Floor means floor"

Introduction "
`midpoint_spec` pins `//` to the name `Int.fdiv` — and a name, by itself,
proves nothing. Step 2 of the arc: prove the *property* that earns the word
**floor**. For a positive divisor `b`, the quotient `q` that `a // b`
returns is the unique integer with

```
b * q  ≤  a  <  b * (q + 1)
```

— the *largest* `q` whose multiple of `b` still fits under `a`. Notice what
is **not** in that sentence: `Int.fdiv`, the interpreter, Lean. It is bare
arithmetic that any skeptic can audit.

Read the theorem's hypotheses; there are two new pieces of kit.

* `hq : arith.floordiv(a, b) ⇓ q` — the **result-binding arrow**: the same
  judgment as `==>`, placed in hypothesis position to *bind* the returned
  value as a name, `q`, that the goal can talk about. (The goal view even
  renders it as `==>` — it is literally the same claim; only the role
  differs.)
* `CallsTo.typed_int_eq` — **determinism**: one call cannot return two
  different integers. Given `hq` and any proved run fact, it pins `q` to
  the value you proved.

The battle plan, in three moves:

1. **Name the value.** Prove the run fact
   `arith.floordiv(a, b) ==> Int.fdiv a b` — `midpoint_spec`'s move, on the
   bare `//`. One catch: with `b` symbolic, symbolic execution stalls at the
   interpreter's `ZeroDivisionError` guard; you must hand `py_prove` the
   fact `b ≠ 0`.
2. **Pin `q`.** `CallsTo.typed_int_eq` welds `hq` to that run fact:
   `q = Int.fdiv a b`.
3. **Open the box.** The **division algorithm** characterizes the floor
   quotient and remainder together. Python's `%` is `Int.fmod`, and your
   inventory now holds the three facts that trap it:
   `Int.fmod_add_fdiv_mul` (remainder plus quotient-times-divisor
   reassembles the dividend), `Int.fmod_nonneg_of_pos` (the remainder is
   `≥ 0`), and `Int.fmod_lt_of_pos` (the remainder is `< b`).

Stage the facts with **`have`** (`have h : P := proof` adds `h : P` to your
context), and finish with **`grind`** — not `omega`, twice over: the goal
multiplies two *variables* (`b * q`), which is outside `omega`'s linear
language, and the binders wear the `PyInt` brand, which `omega` refuses to
look through. `grind` handles both. (You'll meet `omega` on its home turf
next level.)
"

/-- The floor characterization: whenever `arith.floordiv(a, b)` returns `q`
for a positive divisor `b`, then `b * q ≤ a < b * (q + 1)` — `q` is the
*greatest* integer whose multiple of `b` fits under `a`. Stated without
`Int.fdiv`: pure arithmetic, earned from determinism plus the division
algorithm. -/
TheoremDoc floordiv_is_floor as "floordiv_is_floor" in "Python programs"

/-- For every dividend `a`, positive divisor `b`, and value `q` that
`floordiv(a, b)` actually returns: `b * q` lands at or below `a`, and the
next multiple overshoots. Floor really floors. -/
Statement floordiv_is_floor (a b q : PyInt) (hb : 0 < b)
    (hq : arith.floordiv(a, b) ⇓ q) :
    b * q ≤ a ∧ a < b * (q + 1) := by
  Hint (strict := true) "First, the divisor guard: symbolic execution of
  `a // b` will ask whether `b = 0`, and `hb` is not in the shape the guard
  wants. Stage the disequality: `have hb' : b ≠ 0 := by grind`.

  (Why not `by omega`? Try it: `b`'s binder wears the `PyInt` brand, and
  `omega` reports *no usable constraints* — it refuses to look through the
  brand. `grind` unfolds it.)"
  have hb' : b ≠ 0 := by grind
  Hint (strict := true) "Now name the returned value, exactly as
  `midpoint_spec` did for its body:
  `have hrun : arith.floordiv(a, b) ==> Int.fdiv a b := by py_prove [arith, hb']`

  Passing `hb'` alongside the program lets the symbolic run discharge the
  `ZeroDivisionError` guard."
  have hrun : arith.floordiv(a, b) ==> Int.fdiv a b := by py_prove [arith, hb']
  Hint (strict := true) "Two descriptions of one run: `hq` says it returned
  `q`; `hrun` says it returned `Int.fdiv a b`. Determinism welds them:
  `have hqe : q = Int.fdiv a b := CallsTo.typed_int_eq hq hrun`."
  have hqe : q = Int.fdiv a b := CallsTo.typed_int_eq hq hrun
  Hint (strict := true) "The interpreter's work is done — from here on it's
  mathematics. Stage the division algorithm's three facts:

  `have hkey := Int.fmod_add_fdiv_mul a b`

  `have h0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg_of_pos a hb`

  `have h1 : Int.fmod a b < b := Int.fmod_lt_of_pos a hb`"
  have hkey := Int.fmod_add_fdiv_mul a b
  have h0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg_of_pos a hb
  have h1 : Int.fmod a b < b := Int.fmod_lt_of_pos a hb
  Hint (strict := true) "Everything is on the table: `q` *is* the quotient
  (`hqe`), and `hkey`/`h0`/`h1` trap the remainder in `[0, b)`. The sandwich
  follows by arithmetic over those atoms: `grind`."
  grind

Conclusion "
That is what **floor means**: `b * q ≤ a < b * (q + 1)`. No `Int.fdiv` in
the statement, no interpreter, no Lean names — a property any mathematician
can audit, now proved of what the code *does*.

Note the shape of the argument, because it recurs everywhere: **run once,
equate forever.** `py_prove` produced one run fact; determinism
(`CallsTo.typed_int_eq`) converted every other description of that run into
an equation. The program never executed twice.

Fine print: the sandwich is stated for `0 < b`. Floor division floors for
negative divisors too — but the inequalities flip. Try writing the `b < 0`
statement in your head; the proof would be the same three moves.

Step 3 of the arc: spend the property against another language.
"

NewTactic «have» grind
NewTheorem LeanModels.Python.CallsTo.typed_int_eq Int.fmod_add_fdiv_mul
  Int.fmod_nonneg_of_pos Int.fmod_lt_of_pos
NewDefinition ResultArrow Int.fmod
