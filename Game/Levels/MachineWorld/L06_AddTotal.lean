import Game.Levels.MachineWorld.L05_TwoPrograms

open LeanModels LeanModels.Python

World "MachineWorld"
Level 6

Title "Every pair of integers ever"

Introduction "
The smallest program in your inventory, for the biggest claim so far:

```python
def add(a, b):
    return a + b
```

The goal `add(a, b) ==> a + b` quantifies over **two** variables: for every
pair of Python integers — every pair there ever was or will be — `add`
terminates and returns the mathematical sum. Python integers are
arbitrary-precision, so the honest model is genuine `Int`: no overflow
footnote, no word size, no fine print.

Nothing new in your hands. This is the `floordiv_zero` move on a friendlier
program: symbolic execution, program constant in brackets. One line, and
Machine World is yours.
"

/-- `add(a, b) ==> a + b` for all integers — total correctness of `add`:
terminates, no exception, the exact mathematical sum. -/
TheoremDoc add_total as "add_total" in "Python runs"

/-- For all integers `a` and `b` — every pair of integers ever — running
the Python program `add` terminates and returns `a + b`. -/
Statement add_total (a b : PyInt) : add(a, b) ==> a + b := by
  Hint "Two free variables now — even more hopeless for testing, and the
  same one-line move for proving. The bracket names the program constant so
  the tactic can unfold the code."
  Hint (hidden := true) "`py_prove [add]`."
  py_prove [add]

Conclusion "
Machine World, cleared — and look at the arc behind you: you watched a run,
predicted a run, *supplied* a run's missing input, then left running behind
entirely: every `n` (the crash theorem), and now every pair `(a, b)` at
once.

Worth savoring what this last one excludes: no exception, no wrong value,
no overflow — for every pair of integers, including the ones wider than
your RAM.

Next door in Straight-Line World, the programs start making *choices* —
and the proofs stop being one-liners.
"
