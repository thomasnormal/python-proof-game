import Game.Levels.MachineWorld
import Game.Levels.StraightLineWorld

-- Here's what we'll put on the title screen
Title "The Python Proof Game"
Introduction
"
# The Python Proof Game

Prove **real Python programs** correct, in Lean.

Each level's subject is an actual Python file, parsed by CPython's own
parser, shipped into Lean as a syntax tree, and executed by a *verified
interpreter* that is differentially tested against CPython. The theorems are
about the programs as written — floor division, `ZeroDivisionError` and all.

You'll start by running programs *inside proofs* (Machine World), graduate to
symbolic inputs — one theorem covering every integer at once (Straight-Line
World) — and beyond that lie `while` loops and their invariants.

Built on the [lean-surfaces](https://github.com/thomasnormal/lean-surfaces)
framework. No prior Lean experience needed; if you've played the Natural
Number Game, you'll feel at home.
"

Info "
*The Python Proof Game*, built on
[lean-surfaces](https://github.com/thomasnormal/lean-surfaces) —
deep-embedded Python in Lean 4 with a typed spec surface.

The Python programs in this game are real files, extracted with CPython's
`ast` module into JSON envelopes and ingested at build time; the interpreter
giving them meaning is differentially tested against CPython.

Toolchain: leanprover/lean4:v4.33.0-rc1 · lean4game GameServer v4.31.0.

See `GAME_PLAN.md` in the repository for the full world roadmap (Loop World,
and a boss stage proving a routine from the shipped `python-rsa` library).
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Prove real Python programs correct."
CaptionLong "Formal verification of actual Python code: run programs inside
proofs, prove crashes on purpose, then quantify over every input at once.
Honest semantics included — floor division, exceptions, arbitrary-precision
integers. Built on the lean-surfaces framework."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
