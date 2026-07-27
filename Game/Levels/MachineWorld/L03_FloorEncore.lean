import Game.Levels.MachineWorld.L02_FloorRun

open LeanModels LeanModels.Python

World "MachineWorld"
Level 3

Title "Called it"

Introduction "
Before you touch the keyboard: `-3 + -4` is `-7`. What do *you* think
`-7 // 2` is?

Really — commit to a number. Chop-toward-zero (the C reflex) says `-3`.
Floor — one step *down*, toward minus infinity — says `-4`. The true
quotient `-3.5` sits between them, and the floor is the one **below**.

The goal claims `-4`. Don't take its word for it: check it against the
number you just committed to, then let the kernel be the judge.
"

/-- Running `midpoint` on `-3` and `-4` terminates and returns `-4`: the
floor of `-3.5` is the integer *below* it. -/
Statement : midpoint(-3, -4) ==> -4 := by
  Hint "Nothing new in your hands — this is a concrete run, and you know the
  machine move for those."
  Hint (hidden := true) "`py_check` — the kernel runs `midpoint(-3, -4)` and
  lands on `-4`, not `-3`."
  py_check

Conclusion "
Called it — or corrected it; both count. For negative results, *down* means
**away from zero**. That reflex will save you a theorem later.

Next: a program that refuses to return anything at all.
"
