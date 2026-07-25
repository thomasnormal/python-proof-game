import Game.Levels.MachineWorld

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 1

Title "add, for all"

Introduction "
The smallest possible start:

```python
def add(a, b):
    return a + b
```

The goal `add(a, b) ==> a + b` says: for **all** Python integers `a` and `b`,
running `add` terminates and returns the mathematical sum `a + b`. Python
integers are arbitrary-precision, so the honest model is genuine `Int` — no
overflow footnotes.

You watched `py_prove` cross this bridge last world. Now you drive: pass it
the loaded program constant, `add`, in brackets.
"

/-- `add(a, b) ==> a + b` for all integers — total correctness of `add`:
terminates, no exception, exact mathematical sum. -/
TheoremDoc add_total as "add_total" in "Python programs"

/-- For all integers `a` and `b`, running the Python program `add` terminates
and returns `a + b`. -/
Statement add_total (a b : PyInt) : add(a, b) ==> a + b := by
  Hint "Symbolic execution, one call: `py_prove [add]`. The bracket names the
  program constant so the tactic can unfold the code."
  py_prove [add]

Conclusion "
Your first hand-written *for-all* theorem about running Python code.

Worth savoring what it excludes: no exception, no unsupported construct, no
wrong value — for every pair of integers, including the ones wider than your
RAM.
"

NewDefinition add
