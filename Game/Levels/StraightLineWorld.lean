import Game.Levels.StraightLineWorld.L01_AddTotal
import Game.Levels.StraightLineWorld.L02_MidpointSpec
import Game.Levels.StraightLineWorld.L03_FloorMeansFloor
import Game.Levels.StraightLineWorld.L04_PythonIsNotC
import Game.Levels.StraightLineWorld.L05_MidpointNonneg
import Game.Levels.StraightLineWorld.L06_MyAbs
import Game.Levels.StraightLineWorld.L07_Clamp01Boss
import Game.Levels.StraightLineWorld.L08_MachineRises

World "StraightLineWorld"
Title "Straight-Line World"

Introduction "
No more single test cases. In this world the inputs are **symbolic** — every
theorem quantifies over *all* Python integers — and the programs are
loop-free: straight-line bodies, then branches.

Your workhorse is `py_prove`: it symbolically executes the interpreter with
the inputs left abstract. Along the way you'll learn the framework's honesty
rules — Python's `//` is *floor* division and the statements say so, and in
a three-level arc you'll go further: *prove* that floor means floor, then
prove Python and C disagree about `-7 // 2`; preconditions are ordinary
hypotheses; corollaries are derived by arithmetic,
never by re-running code — and at the end, a boss fight at the exact
documented boundary where the automation stops and you take over. Then, in
the coda, everything you did by hand comes back *generated*: your first
meeting with `py_vcgen`, the machine that carries the rest of the game.
"
