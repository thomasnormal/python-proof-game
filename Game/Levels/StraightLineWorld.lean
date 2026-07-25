import Game.Levels.StraightLineWorld.L01_AddTotal
import Game.Levels.StraightLineWorld.L02_MidpointSpec
import Game.Levels.StraightLineWorld.L03_MidpointNonneg
import Game.Levels.StraightLineWorld.L04_MyAbs
import Game.Levels.StraightLineWorld.L05_Clamp01Boss

World "StraightLineWorld"
Title "Straight-Line World"

Introduction "
No more single test cases. In this world the inputs are **symbolic** — every
theorem quantifies over *all* Python integers — and the programs are
loop-free: straight-line bodies, then branches.

Your workhorse is `py_prove`: it symbolically executes the interpreter with
the inputs left abstract. Along the way you'll learn the framework's honesty
rules — Python's `//` is *floor* division and the statements say so;
preconditions are ordinary hypotheses; corollaries are derived by arithmetic,
never by re-running code — and at the end, a boss fight at the exact
documented boundary where the automation stops and you take over.
"
