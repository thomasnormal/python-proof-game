import Game.Levels.StraightLineWorld.L06_MyAbs

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 7

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
can no longer attack. Try `py_prove [ag_clamp01]` if you like: it fails *on
purpose*, with a short note that the body left interpreter state unresolved,
pointing at the heavier tools — not a screenful of half-digested interpreter
state. Automation that fails politely at its documented boundary is a
feature; now you get to be the automation.

The house pattern for multi-`if` bodies:

1. **Fuel — and fuel comes first.** Under every `==>` goal sits an
   existential: “*some* step budget finishes this run.” Until a concrete
   budget is on the table there is no run to execute, so no split or
   symbolic step can even begin — which is why this move must open the
   proof. The `⟨…, …⟩` is the **anonymous constructor** (new in your
   inventory): `refine ⟨32, ?_⟩` supplies the witness `32` and leaves the
   run itself open as `?_`. (`py_check` and `py_prove` have been donating
   the fuel for you all game; now you do it yourself.)
2. **Decide the branches up front**: `by_cases h1 : x < 0`, then
   `by_cases h2 : 1 < x` — four cases, each with the tests answered.
3. **Execute**: `py_simp [callFunction, ag_clamp01, h1, h2]` — symbolic
   execution with your case facts resolving both tests.
4. **Finish**: `grind` — *not* `omega`: the `by_cases` comparisons elaborate
   over the `PyInt` brand, whose head type `omega` refuses to look through
   (the same brand-blindness you met in “Floor means floor”);
   `grind` matches up to reducible unfolding and closes all four cases.

You can chain the case splits with **`<;>`** — “then, on every goal just
produced…”, also new in your inventory — and write the whole thing in one
breath, or take it step by step.
"

/-- `ag_clamp01.clamp01(x) ==> max 0 (min 1 x)` for every integer — proved
by hand at the documented boundary of `py_prove`'s recipe. -/
TheoremDoc clamp01_total as "clamp01_total" in "Python programs"

/-- For every integer `x`, running `clamp01` terminates and returns `x`
clamped to `[0, 1]` — that is, `max 0 (min 1 x)`. -/
Statement clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  Hint "Step 1 — commit fuel, and commit it *first*: the goal is secretly an
  existential (“some fuel finishes this run”), so nothing can execute the
  body until a concrete budget is on the table. The anonymous constructor
  hands it over: `refine ⟨32, ?_⟩` — witness `32`, run left open as `?_`."
  Branch
    by_cases h1 : x < 0
    Hint (strict := true) "Splitting before donating fuel leaves both cases
    staring at the bare `==>` goal — an existential (“*some* fuel finishes
    this run”) that `py_simp` cannot open. The fuel witness has to come
    *first*: start over, open with `refine ⟨32, ?_⟩`, and split after."
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

One more stop before the loops. Everything you just did — fuel, branch
facts, symbolic runs, the sweep — was a *procedure*. And procedures can be
mechanized. Next level, the machine rises.
"

NewTactic refine py_simp by_cases «<;>»
NewDefinition ag_clamp01 LeanModels.Python.callFunction AnonymousConstructor
