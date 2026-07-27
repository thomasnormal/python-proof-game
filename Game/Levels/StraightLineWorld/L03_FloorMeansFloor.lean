import Game.Levels.StraightLineWorld.L02_MidpointSpec

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 3

Title "Floor means floor"

Introduction "
`midpoint_spec` pins `//` to the name `Int.fdiv` — and a name, by itself,
proves nothing. Step 2 of the arc: prove the *property* that earns the word
**floor**. For a positive divisor `b`, the quotient `q` that `a // b`
returns satisfies

```
b * q  ≤  a  <  b * (q + 1)
```

— the *largest* `q` whose multiple of `b` still fits under `a`. Nothing
there mentions `Int.fdiv`, the interpreter, or Lean: bare arithmetic any
skeptic can audit.

Two new pieces of kit sit in the hypotheses — each has an inventory tile
worth reading: `hq : arith.floordiv(a, b) ⇓ q` is the **result-binding
arrow** (the same judgment as `==>`, placed in hypothesis position to *bind*
the returned value as `q`), and `CallsTo.typed_int_eq` is **determinism**
(one call cannot return two different integers).

The battle plan: **name the value** (prove the run fact
`… ==> Int.fdiv a b`, handing `py_prove` the divisor guard `b ≠ 0`), **pin
`q`** (determinism welds `hq` to the run fact), **open the box** (stage the
three division-algorithm facts with **`have`**, then **`grind`** — not
`omega`: `b * q` is nonlinear and the binders wear the `PyInt` brand). The
hints stage every move.
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
  Hint (strict := true) (hidden := true) "Now name the returned value,
  exactly as `midpoint_spec` did for its body:
  `have hrun : arith.floordiv(a, b) ==> Int.fdiv a b := by py_prove [arith, hb']`

  Passing `hb'` alongside the program lets the symbolic run discharge the
  `ZeroDivisionError` guard."
  have hrun : arith.floordiv(a, b) ==> Int.fdiv a b := by py_prove [arith, hb']
  Hint (strict := true) (hidden := true) "Two descriptions of one run: `hq`
  says it returned `q`; `hrun` says it returned `Int.fdiv a b`. Determinism
  welds them:
  `have hqe : q = Int.fdiv a b := CallsTo.typed_int_eq hq hrun`."
  have hqe : q = Int.fdiv a b := CallsTo.typed_int_eq hq hrun
  Hint (strict := true) (hidden := true) "The interpreter's work is done —
  from here on it's mathematics. Stage the division algorithm's three facts:

  `have hkey := Int.fmod_add_fdiv_mul a b`

  `have h0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg_of_pos a hb`

  `have h1 : Int.fmod a b < b := Int.fmod_lt_of_pos a hb`"
  have hkey := Int.fmod_add_fdiv_mul a b
  have h0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg_of_pos a hb
  have h1 : Int.fmod a b < b := Int.fmod_lt_of_pos a hb
  Hint (strict := true) (hidden := true) "Everything is on the table: `q`
  *is* the quotient (`hqe`), and `hkey`/`h0`/`h1` trap the remainder in
  `[0, b)`. The sandwich follows by arithmetic over those atoms: `grind`."
  grind

Conclusion "
That is what **floor means**: `b * q ≤ a < b * (q + 1)` — a property any
mathematician can audit, now proved of what the code *does*.

Note the shape, because it recurs everywhere: **run once, equate forever.**
One run fact, then determinism converts every other description of that run
into an equation. The program never executed twice.

Step 3 of the arc: spend the property against another language.
"

NewTactic «have» grind
NewTheorem LeanModels.Python.CallsTo.typed_int_eq Int.fmod_add_fdiv_mul
  Int.fmod_nonneg_of_pos Int.fmod_lt_of_pos
NewDefinition ResultArrow Int.fmod
