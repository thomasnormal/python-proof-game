import Game.Levels.MachineWorld.L05_CrashEncore

open LeanModels LeanModels.Python

World "MachineWorld"
Level 6

Title "The bridge: every input at once"

Introduction "
Back to `floordiv`:

```python
def floordiv(a, b):
    return a // b
```

Last level you proved `floordiv(-3, 0)` raises. Nice. What about
`floordiv(8, 0)`? `floordiv(10¹⁰⁰, 0)`?

Look at the goal: `a` is now a **variable** — `(a : PyInt)` means *every*
Python integer at once. `py_check` is no use here, and it knows it: try it,
and it refuses on sight — a free variable means there is nothing concrete to
run, and it tells you whose territory you've crossed into. You cannot run
infinitely many test cases.

You need *symbolic execution*: walk the interpreter through the body with `a`
left abstract. The tactic `py_prove [arith]` does exactly that — pass it the
loaded program constant so it can unfold the code.

This once, the proof is already written in the editor. Read it, run it,
believe it. From the next world on, you type it yourself.
"

/-- `arith.floordiv(a, 0) ==>! .zeroDivisionError` for **every** integer `a`
— the first symbolic statement: infinitely many crashes, one proof. -/
TheoremDoc floordiv_zero as "floordiv_zero" in "Python runs"

/-- For **every** integer `a`, running `floordiv` on `a` and `0` terminates
by raising `ZeroDivisionError`. -/
Statement floordiv_zero (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError := by
  Template
    py_prove [arith]

Conclusion "
One tactic, infinitely many crashes.

`py_prove` committed a fuel budget, symbolically executed `a // 0` with `a`
abstract, and discharged what was left. The result is a statement no amount
of testing reaches: **for all** `a`.

That's Machine World cleared. Next: Straight-Line World, where the *values*
go symbolic too — its first patient, `add`, is already in your inventory.
"

NewTactic py_prove
NewHiddenTactic Template
NewDefinition add
