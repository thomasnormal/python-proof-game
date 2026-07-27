import Game.Levels.MachineWorld.L01_TriRun
import Game.Levels.MachineWorld.L02_FloorRun
import Game.Levels.MachineWorld.L03_FloorEncore
import Game.Levels.MachineWorld.L04_ModRaise
import Game.Levels.MachineWorld.L05_CrashEncore
import Game.Levels.MachineWorld.L06_SymbolicBridge

World "MachineWorld"
Title "Machine World"

Introduction "
Welcome to the machine room.

Real Python programs — parsed by CPython itself, shipped into Lean as syntax
trees — run here on a *verified interpreter*: an ordinary Lean definition,
differentially tested against CPython. In this world every claim is about one
**concrete run**: this input, this output (or this exception).

Concrete claims have a beautiful property: the proof is just *running the
program inside the proof*. You'll provide the fuel; the kernel does the rest.

By the last level, you'll hit the wall every tester knows — you can't run
infinitely many test cases — and walk across the bridge that fixes it.
"
