import Game.Levels.MachineWorld.L03_FloorEncore

open LeanModels LeanModels.Python

World "MachineWorld"
Level 4

Title "It crashes. Prove it."

Introduction "
From a little arithmetic module:

```python
def mod(a, b):
    return a % b
```

What does `mod(7, 0)` return? Nothing. It **raises** `ZeroDivisionError`.

In this framework, runtime errors are not failures of the semantics — they
*are* the semantics. The judgment `arith.mod(7, 0) ==>! .zeroDivisionError`
says: the call terminates *by raising* `ZeroDivisionError`. Exceptions are
specified behavior, and you can prove them.

(The dotted name `arith.mod` just means: function `mod` in the loaded module
`arith`.)

The proof is the same honest shape as before: some fuel makes the run finish
— just not with a value this time. `py_check` handles both endings.
"

/-- `arith.mod(7, 0) ==>! .zeroDivisionError` — a crash, proved on
purpose. -/
TheoremDoc mod_seven_zero as "mod_seven_zero" in "Python runs"

/-- Running `mod` from the `arith` module on `7` and `0` terminates by
raising `ZeroDivisionError`. -/
Statement mod_seven_zero : arith.mod(7, 0) ==>! .zeroDivisionError := by
  Hint "`==>!` is also a concrete run — it just ends in
  `.exn .zeroDivisionError` instead of a value. `py_check` proves crashes
  too."
  py_check

Conclusion "
You proved a crash. On purpose. With `py_check`.

Notice what this rules out: `mod(7, 0)` does not loop forever, does not
return some junk value, does not hit an unsupported construct — it raises
exactly `ZeroDivisionError`. Try getting *that* guarantee from a unit test.
"

NewDefinition LeanModels.Python.Raises arith
