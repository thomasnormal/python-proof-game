import Game.Levels.MachineWorld.L01_TriRun
import Game.Levels.MachineWorld.L02_FloorRun
import Game.Levels.MachineWorld.L03_FindTheInput
import Game.Levels.MachineWorld.L04_FloordivZero
import Game.Levels.MachineWorld.L05_TwoPrograms
import Game.Levels.MachineWorld.L06_AddTotal

World "MachineWorld"
Title "Machine World"

Introduction "
Welcome to the machine room.

Real Python programs — parsed by CPython itself, shipped into Lean as syntax
trees — run here on a *verified interpreter*: an ordinary Lean definition,
differentially tested against CPython.

The first claims are about one **concrete run** each: this input, this
output. Concrete claims have a beautiful property: the proof is just
*running the program inside the proof*. But this world does not stop there.
By its midpoint you'll hit the wall every tester knows — you cannot run
infinitely many test cases — watch the concrete tool refuse on principle,
and prove your first theorem about **every input at once**.

Meet the judgment; then meet infinity.
"
