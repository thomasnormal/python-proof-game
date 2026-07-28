import Game.Levels.MachineWorld.L04_FloordivZero

open LeanModels LeanModels.Python

World "MachineWorld"
Level 5

Title "Two programs, one answer"

Introduction "
Back to return values — with both of your day-one programs on stage:

```python
def tri(n):              # 0 + 1 + 2 + ⋯ + n
    ...

def midpoint(a, b):
    return (a + b) // 2
```

The goal: `∃ v, tri(4) ==> v ∧ midpoint(13, 7) ==> v` — one value `v` that
**both** runs produce. Two predictions this time: `tri(4)` is banked from
level 1, and `midpoint(13, 7)` is a fresh floor division. Work them both
out — do they really meet?

Your witness move opens the `∃`, and the anonymous constructor swallows the
`∧` too: `refine ⟨your_v, ?_, ?_⟩` leaves **two** goals, one per program.
You could `py_check` each in turn. Or say it once — `tac₁ <;> tac₂` runs
`tac₂` on **every** goal `tac₁` just produced. One witness, one sweep:

`refine ⟨your_v, ?_, ?_⟩ <;> py_check`
"

/-- Two different programs, one common answer: a single witness `v` closes
both `tri(4)` and `midpoint(13, 7)`. -/
Statement : ∃ v : PyInt, tri(4) ==> v ∧ midpoint(13, 7) ==> v := by
  Hint "Run both in your head: `tri(4)` is level 1's theorem, and
  `midpoint(13, 7)` is `20 // 2` — no sign traps this time. If they agree,
  commit the common value with `refine ⟨your_v, ?_, ?_⟩`, then sweep both
  goals with `<;> py_check`."
  Hint (hidden := true) "`refine ⟨10, ?_, ?_⟩ <;> py_check` — `0+1+2+3+4`
  and `(13 + 7) // 2` both land on `10`."
  refine ⟨10, ?_, ?_⟩ <;> py_check

Conclusion "
Two machines, one witness, one sweep. `⟨…⟩` flattened the `∃` and the `∧`
in a single stroke, and `<;>` aimed `py_check` at both goals at once. Keep
both habits — a later boss forks four ways.

One program in your deck hasn't been touched since it landed: `add`. Two
inputs, no tricks — and your finale makes it infinite in *two* directions
at once.
"

NewTactic «<;>»
NewDefinition add
