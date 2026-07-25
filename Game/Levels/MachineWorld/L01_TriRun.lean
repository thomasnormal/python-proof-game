import Game.Doc

open LeanModels LeanModels.Python

World "MachineWorld"
Level 1

Title "Run it"

Introduction "
Here is a real Python program. Not pseudocode — this exact file went through
CPython's own parser:

```python
def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total
```

Its syntax tree now lives inside Lean as a constant called `tri`, and a
*verified interpreter* — an ordinary, executable Lean definition — gives it
meaning.

Your goal, `tri(4) ==> 10`, is a theorem: **running `tri` on `4` terminates
and returns `10`.**

One honest detail hides under the arrow: the interpreter takes *fuel* (a step
budget), and `==>` says “*some* amount of fuel finishes the run”. So the proof
has two moves: hand over fuel, then let the machine run.

Use `refine ⟨100, ?_⟩` to donate 100 units of fuel, and see what's left.
"

/-- `tri(4) ==> 10` — one concrete run of the Python program `tri`,
certified by kernel computation. -/
TheoremDoc tri_four as "tri_four" in "Python runs"

/-- Running the Python program `tri` on the input `4` terminates and
returns `10`. -/
Statement tri_four : tri(4) ==> 10 := by
  Hint "`==>` says: *some* fuel makes this run finish with `10`. Offer a
  generous budget with `refine ⟨100, ?_⟩` — extra fuel is harmless, a
  finished run keeps its result."
  refine ⟨100, ?_⟩
  Hint "Look at that goal: it says the interpreter — a Lean *definition* —
  applied to `tri`, the input `4`, and your fuel, equals `.ok 10`. Both sides
  are closed terms. Ask Lean to simply compute them: `rfl`."
  rfl

Conclusion "
The kernel just *ran the Python program inside the proof*. Five loop
iterations, executed by `rfl`. No test framework, no mocks — a theorem.

Of course, `tri(4) ==> 10` is one test case wearing a fancy hat. The rest of
this game is about earning the un-fancy hats: `tri(n)` for *every* `n`.
"

NewTactic refine rfl
NewDefinition LeanModels.Python.CallsTo tri
