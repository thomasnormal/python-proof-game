import Game.Levels.MachineWorld.L03_FindTheInput

open LeanModels LeanModels.Python

World "MachineWorld"
Level 4

Title "Infinitely many tests, one line"

Introduction "
From a little arithmetic module:

```python
def floordiv(a, b):
    return a // b
```

What does `floordiv(n, 0)` do? It **raises** `ZeroDivisionError` — and in
this framework, runtime errors are not failures of the semantics, they *are*
the semantics. The judgment `==>!` says: the run terminates *by raising*.
(The dotted `arith.floordiv` means: function `floordiv` of the loaded
module `arith`.)

`py_check` would happily prove one case — `floordiv(-3, 0)`, say. But look
at the goal: `n` is a **variable**. `(n : PyInt)` means *every* Python
integer at once — infinitely many test cases in one claim. Try `py_check`:
it refuses on sight. A free variable means there is nothing concrete to
run, and no test suite on earth runs them all.

Meet **`py_prove`**: *symbolic* execution. It walks the interpreter through
the body with `n` left abstract, so one run stands for all of them. Pass it
the loaded program constant in brackets, so it can unfold the code.
"

/-- `arith.floordiv(n, 0) ==>! .zeroDivisionError` for **every** integer `n`
— the game's first symbolic theorem: infinitely many crashes, one line. -/
TheoremDoc floordiv_zero as "floordiv_zero" in "Python runs"

/-- For **every** integer `n`, running `floordiv` on `n` and `0` terminates
by raising `ZeroDivisionError` — no test suite can check this; a proof
can. -/
Statement floordiv_zero (n : PyInt) : arith.floordiv(n, 0) ==>! .zeroDivisionError := by
  Hint "Feel the wall first if you like: `py_check` refuses any goal with a
  free variable in it. The symbolic tool takes the program constant in
  brackets."
  Hint (hidden := true) "`py_prove [arith]`."
  py_prove [arith]

Conclusion "
One line, infinitely many crashes: `py_prove` committed a fuel budget,
executed `n // 0` with `n` left abstract, and discharged what remained.

Sit with what you just did. A test suite running a billion cases a second
since the big bang would still be at zero percent of this statement. You
cleared it in one line — that is what *formal* buys.

Also proved en passant: `floordiv(n, 0)` never loops forever, never returns
junk — it raises exactly `ZeroDivisionError`, for every `n` there is.
"

NewTactic py_prove
NewDefinition LeanModels.Python.Raises arith
