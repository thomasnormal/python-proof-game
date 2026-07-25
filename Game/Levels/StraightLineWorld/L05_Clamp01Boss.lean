import Game.Levels.StraightLineWorld.L04_MyAbs

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 5

Title "Boss: clamp01"

Introduction "
The boss of Straight-Line World:

```python
def clamp01(x):
    if x < 0:
        return 0
    if x > 1:
        return 1
    return x
```

**Two sequential `if`s** — and that breaks `py_prove`: its recipe splits *one*
surviving `if`; the second one gets mangled into a disjunction that `split`
can no longer attack. Try `py_prove [ag_clamp01]` if you like. It will fail.
Automation that fails loudly at its documented boundary is a feature; now you
get to be the automation.

The house pattern for multi-`if` bodies:

1. **Fuel**: `refine ⟨32, ?_⟩` — commit a budget, like in Machine World.
2. **Decide the branches up front**: `by_cases h1 : x < 0`, then
   `by_cases h2 : 1 < x` — four cases, each with the tests answered.
3. **Execute**: `py_simp [callFunction, ag_clamp01, h1, h2]` — symbolic
   execution with your case facts resolving both tests.
4. **Finish**: `grind` — *not* `omega`: the `by_cases` comparisons elaborate
   over the `PyInt` brand, whose head type `omega` refuses to look through;
   `grind` matches up to reducible unfolding and closes all four cases.

You can chain the case splits with `<;>` (“then, on every goal produced…”)
and write the whole thing in one breath, or take it step by step.
"

/-- `ag_clamp01.clamp01(x) ==> max 0 (min 1 x)` for every integer — proved
by hand at the documented boundary of `py_prove`'s recipe. -/
TheoremDoc clamp01_total as "clamp01_total" in "Python programs"

/-- For every integer `x`, running `clamp01` terminates and returns `x`
clamped to `[0, 1]` — that is, `max 0 (min 1 x)`. -/
Statement clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  Hint "Step 1 — commit fuel: `refine ⟨32, ?_⟩`."
  refine ⟨32, ?_⟩
  Hint "Step 2 — decide both tests before executing:
  `by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind`

  (Or split step by step — `by_cases h1 : x < 0` first, and work the four
  goals by hand.)"
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind

Conclusion "
Boss down. You just did by hand what `py_prove` does inside — fuel, symbolic
execution, case analysis, arithmetic — on a shape the automation honestly
refuses.

That's Straight-Line World cleared. Beyond this point lies **Loop World**:
`while` loops, where no finite case split saves you and you'll meet the two
ideas no tactic can invent for you — the *invariant* and the *decreasing
measure*. See you there.
"

NewTactic py_simp by_cases grind omega
NewDefinition ag_clamp01 LeanModels.Python.callFunction
