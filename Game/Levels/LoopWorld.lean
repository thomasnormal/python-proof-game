import Game.Levels.LoopWorld.L01_ReadTheProof
import Game.Levels.LoopWorld.L02_InventInvariant
import Game.Levels.LoopWorld.L03_OddSum
import Game.Levels.LoopWorld.L04_SumTo
import Game.Levels.LoopWorld.L05_Gcd
import Game.Levels.LoopWorld.L06_NestedBoss

World "LoopWorld"
Title "Loop World"

Introduction "
`while` loops. The programs are one honest step from real: countdowns,
Euclid's algorithm, trial division — and no finite case split covers any of
them, because the number of iterations depends on the input.

What covers them is the oldest idea in program verification: the **loop
invariant** (a fact every iteration preserves) and the **decreasing
measure** (a number every iteration shrinks). These two are the content no
tactic can invent. Everything else — walking the code, splicing the symbolic
runs, forking the branches — is `py_vcgen`'s job, and what it leaves you is
pure mathematics, tagged by role: `init`, `preserve`, `dec`, `ret`.

You'll read one loop proof, then invent your own invariants: for a square,
for a countdown that shadows its own argument, for Euclid — and for the
boss, a nested loop with a `break`, where you'll state what's true at the
moment of escape.
"
