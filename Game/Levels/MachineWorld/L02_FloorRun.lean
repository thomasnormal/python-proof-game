import Game.Levels.MachineWorld.L01_TriRun

open LeanModels LeanModels.Python

World "MachineWorld"
Level 2

Title "The floor is not the ceiling"

Introduction "
A one-liner this time:

```python
def midpoint(a: int, b: int) -> int:
    return (a + b) // 2
```

Quick — before you look at the goal below, work out `midpoint(3, -4)` in
your head: `3 + (-4)` is `-1`; now `-1 // 2` in *Python*. Lock in your
answer.

Python's `//` is *floor* division, not truncation toward zero — think about
which way `-1 // 2` rounds before the machine tells you.

Prove the run. Same move as before: make the machine run it.
"

/-- `midpoint(3, -4) ==> -1` — floor division rounds toward minus
infinity. -/
TheoremDoc midpoint_three_negfour as "midpoint_three_negfour" in "Python runs"

/-- Running `midpoint` on `3` and `-4` terminates and returns `-1` — floor
division rounds toward minus infinity. -/
Statement midpoint_three_negfour : midpoint(3, -4) ==> -1 := by
  Hint "A concrete run again — same opening move as `tri(4)`."
  Hint (hidden := true) "`py_check` — the kernel computes the run and lands
  on `-1`."
  py_check

Conclusion "
The machine's verdict: `-1`. **Not** `0` — Python's `//` rounds toward minus
infinity, not toward zero. If you guessed `0`, you were thinking like C; the
interpreter under this game thinks like CPython, because it is tested
*against* CPython.

Remember this level — in Straight-Line World the floor-vs-truncation
distinction stops being a party trick and becomes part of an honest theorem
*statement*.

Two levels in, a pattern: level one you *watched* the machine; this level
you *predicted* it. Next level the goal loses a piece — and you **supply**
it.
"
