import Game.Levels.MachineWorld.L04_ModRaise

open LeanModels LeanModels.Python

World "MachineWorld"
Level 5

Title "Crash, encore"

Introduction "
`mod(7, 0)` raised. Its sibling in the `arith` module:

```python
def floordiv(a, b):
    return a // b
```

Two questions before you prove anything. First: does `floordiv(-3, 0)` crash
too, or does floor division deal with zero some other way? Second — the one
no unit test ever pins down — *which* exception, exactly? `//` and `%` are
different operations; nothing in the syntax forces them to fail the same
way.

The goal commits to an answer on both counts. Check it against your guesses,
then let the machine settle it.
"

/-- Running `floordiv` on `-3` and `0` terminates by raising
`ZeroDivisionError` — the division family's house error. -/
Statement : arith.floordiv(-3, 0) ==>! .zeroDivisionError := by
  Hint "`==>!` is still a concrete run — it just ends in an exception. You
  own the tactic that proves both endings."
  Hint (hidden := true) "`py_check` — it executes the call in-kernel and
  matches the raised `ZeroDivisionError`."
  py_check

Conclusion "
Same crash, same one-line proof: `ZeroDivisionError` is the whole division
family's answer to zero.

You proved it for `-3`. What about `8`? `10¹⁰⁰`? That itch has a name — and
the next level scratches it.
"
