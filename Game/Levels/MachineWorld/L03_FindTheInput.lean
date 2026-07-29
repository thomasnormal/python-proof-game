import Game.Levels.MachineWorld.L02_FloorRun

open LeanModels LeanModels.Python

World "MachineWorld"
Level 3

Title "Find the input"

Introduction "
Back to the opening program:

```python
def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total
```

So far every goal named both the input and the output, and you supplied
belief. This goal has a hole where the input should be:

`∃ n, tri(n) ==> 15` — *there **exists** an `n`* on which `tri` returns
`15`.

No machine hunts the witness for you: finding it is your half of the proof.
Run the loop in your head — `tri` adds `0 + 1 + 2 + ⋯ + n` — and you even
hold a data point: level 1 proved `tri(4) ==> 10`. Which `n` lands exactly
on `15`?

Committing a witness has a move: `refine ⟨your_n, ?_⟩`. The `⟨…⟩` is the
**anonymous constructor** — it packages *a witness together with a proof
about it* — and the `?_` leaves the proof part open. What remains after
that is a concrete run, and you own the tactic for concrete runs.
"

/-- There is an input on which `tri` returns `15` — and the proof must
*name* it: witness first, then one concrete run. -/
Statement : ∃ n : PyInt, tri(n) ==> 15 := by
  Hint "Count `0 + 1 + 2 + ⋯` until it hits `15` — or start from the banked
  fact `tri(4) ==> 10` and ask how many more loop turns you need. Then
  commit: `refine ⟨your_n, ?_⟩`."
  Branch
    refine ⟨4, ?_⟩
    Hint "`tri(4)` was level 1's theorem — it returns `10`, not `15`, and
    `py_check` won't certify a false run — it names what it actually
    computed: *the run produced `10` but the goal claims `15`*. Undo, take
    one more loop turn, and raise your witness."
  refine ⟨5, ?_⟩
  Hint "The `∃` is gone — your witness sits in the goal, which is concrete
  again. Finish with the machine move."
  Hint (hidden := true) "`py_check` — the kernel runs `tri(5)` and lands on
  `0+1+2+3+4+5 = 15`. (If it disagrees, it'll tell you exactly what it
  computed instead: undo and recount.)"
  py_check

Conclusion "
`⟨5, _⟩` — you supplied the data, the machine supplied the certainty.

And here's the secret: you've been playing this level since the beginning.
Every `==>` claim is itself an existential — *some fuel finishes the run* —
and `py_check` has quietly donated that witness every single time. Witness
first, proof second is not a new trick; it is the game's oldest move, now
in your hands.

Next: a claim so big no machine that merely *runs* things can touch it.
"

NewTactic refine
NewDefinition AnonymousConstructor
