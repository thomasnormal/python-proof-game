import Game.Levels.StraightLineWorld.L01_MidpointSpec
import Game.Levels.StraightLineWorld.L02_FloorMeansFloor
import Game.Levels.StraightLineWorld.L03_PythonIsNotC
import Game.Levels.StraightLineWorld.L04_MidpointDiv
import Game.Levels.StraightLineWorld.L05_MyAbs
import Game.Levels.StraightLineWorld.L06_MyMax
import Game.Levels.StraightLineWorld.L07_Clamp01Boss
import Game.Levels.StraightLineWorld.L08_MachineRises

World "StraightLineWorld"
Title "Straight-Line World"

Introduction "
Machine World ended with programs that always do the same thing. In this
world the programs **choose** — loop-free bodies, then branches — and the
proofs stop being one-liners: every theorem still quantifies over *all*
Python integers, but now the statements carry names, get banked, and get
*spent*.

`py_prove` meets its real material here. You'll learn the framework's
honesty rules — Python's `//` is *floor* division and the statements say so,
and in a three-level arc you'll go further: *prove* that floor means floor,
then prove Python and C disagree about `-7 // 2`; preconditions are ordinary
hypotheses; corollaries are derived by arithmetic, never by re-running code.
At the end waits a boss fight at the exact documented boundary where the
automation stops and you assemble a four-case proof by hand. Then, in the
coda, everything you did by hand comes back *generated*: your first meeting
with `py_vcgen`, the machine that carries the rest of the game.
"
