import Game.Levels.StraightLineWorld.L06_MyMax

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 7

Title "Boss: clamp01"

Introduction "
The boss of Straight-Line World — the **toughest level yet**, and the first
proof you assemble entirely by hand:

```python
def clamp01(x):
    if x < 0:
        return 0
    if x > 1:
        return 1
    return x
```

**Two sequential `if`s** — the documented boundary of `py_prove`. Try
`py_prove [ag_clamp01]` if you like: it fails *on purpose*, with a short
note pointing at the heavier tools. Now you get to be the automation.

The house pattern for multi-`if` bodies — two new tools, two old moves:

1. **Fuel first.** Every `==>` goal hides an existential — “*some* step
   budget finishes this run” — and nothing executes until a budget is on
   the table. The same witness move from Machine World, `refine ⟨32, ?_⟩` —
   this time the witness is *fuel*.
2. **Decide the branches up front** with the new `by_cases` — four cases,
   each with its tests answered.
3. **Execute** each with the new `py_simp`, handing it `callFunction` and your case facts.
4. **Finish** with `grind` — *not* `omega`: the case facts wear the `PyInt`
   brand.

Chain the stages with `<;>` — your two-program sweep, four goals wide —
one breath, or step by step. The hints stage it either way.
"

/-- `ag_clamp01.clamp01(x) ==> max 0 (min 1 x)` for every integer — proved
by hand at the documented boundary of `py_prove`'s recipe. -/
TheoremDoc clamp01_total as "clamp01_total" in "Python programs"

/-- For every integer `x`, running `clamp01` terminates and returns `x`
clamped to `[0, 1]` — that is, `max 0 (min 1 x)`. -/
Statement clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  Hint "Step 1 — commit fuel, and commit it *first*: the goal is secretly an
  existential (“some fuel finishes this run”), so nothing can execute the
  body until a concrete budget is on the table. Machine World's witness move
  hands it over: `refine ⟨32, ?_⟩` — witness `32`, run left open as `?_`."
  Branch
    by_cases h1 : x < 0
    Hint (strict := true) "Splitting before donating fuel leaves both cases
    staring at the bare `==>` goal — an existential (“*some* fuel finishes
    this run”) that `py_simp` cannot open. The fuel witness has to come
    *first*: start over, open with `refine ⟨32, ?_⟩`, and split after."
  refine ⟨32, ?_⟩
  Hint "Step 2 — decide both tests before executing: split on `x < 0`, then
  on `1 < x`, then `py_simp` with the program, `callFunction`, and your two
  case facts, then sweep with `grind`. Chain it all with `<;>`, or split
  step by step and work the four goals by hand."
  Hint (hidden := true) "The one-breath version:
  `by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind`"
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind

Conclusion "
Boss down — and the war is won: nothing harder stands between you and the
loops. You just did by hand what `py_prove` does inside, on a shape the
automation honestly refuses.

One easy stop before the loops. Everything you just did — fuel, branch
facts, symbolic runs, the sweep — was a *procedure*. And procedures can be
mechanized. Next level, the machine rises.
"

NewTactic py_simp by_cases
NewDefinition ag_clamp01 LeanModels.Python.callFunction
