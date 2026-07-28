# The Python Proof Game

A [lean4game](https://github.com/leanprover-community/lean4game/) that teaches
formal verification of **real Python programs**, built on the
[lean-surfaces](https://github.com/thomasnormal/lean-surfaces) framework:
actual Python files, parsed by CPython's own parser, deep-embedded in Lean 4
and executed by a verified interpreter that is differentially tested against
CPython.

You'll prove theorems like

```lean
theorem tri_four : tri(4) ==> 10                     -- run a loop inside a proof
example : ∃ n : PyInt, tri(n) ==> 15                 -- hunt the witness yourself
theorem floordiv_zero (n : PyInt) : arith.floordiv(n, 0) ==>! .zeroDivisionError
theorem add_total (a b : PyInt) : add(a, b) ==> a + b   -- ... for EVERY input
theorem midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2
```

in the playful style of the Natural Number Game.

## Contents

- **World 1 — Machine World** (6 levels): the kernel executes Python inside
  your proofs — watch a run, predict a run, then *supply* what the goal
  withholds: a witness input, a crash theorem over every integer at once, a
  common answer two programs share.
- **World 2 — Straight-Line World** (8 levels): programs that choose;
  the floor arc (prove `//` floors, then prove Python and C disagree),
  preconditions as hypotheses, and a boss fight at the documented boundary
  of the automation — then the boss fight, mechanized (`py_vcgen`).
- **World 3 — Loop World** (9 levels): `while` loops; invent invariants and
  decreasing measures, survive a shadowed argument and a branch in the loop
  body, prove Euclid, cash out a corollary, and beat a nested-loop,
  `break`-and-`return` boss.
- **World 4** (RSA World): designed in [GAME_PLAN.md](GAME_PLAN.md), not
  yet built.

`GAME_PLAN.md` also records the toolchain reconciliation (this game runs the
lean4game `v4.31.0` GameServer on Lean `v4.33.0-rc1`) and the publication
checklist.

## Build

```sh
lake update   # usually unnecessary — the manifest is committed
lake build    # builds levels, runs MakeGame checks, writes .lake/gamedata/
```

Always build from the repo root: the Python programs are ingested at build
time from `GameAssets/envelopes/*.json`, resolved relative to the working
directory. A fast re-check of all level proofs outside the game machinery:
`lake env lean GameAssets/smoke_test.lean`.

To play locally in a browser, use the lean4game development setup
([running a game locally](https://github.com/leanprover-community/lean4game/blob/main/doc/running_locally.md)):
devcontainer, Codespaces, or a local `lean4game` clone with `npm start`, then
open `http://localhost:3000/#/g/local/python-proof-game`.

## Layout

| Path | What |
|---|---|
| `Game.lean` | Game metadata + `MakeGame` |
| `Game/Programs.lean` | All `load_program` ingestions + `#py_check` non-vacuity runs |
| `Game/Doc.lean` | Inventory docs: tactics, judgments, programs |
| `Game/Levels/MachineWorld/` | World 1 levels |
| `Game/Levels/StraightLineWorld/` | World 2 levels |
| `Game/Levels/LoopWorld/` | World 3 levels |
| `GameAssets/envelopes/` | Bundled JSON envelopes + the `.py` sources they were extracted from |
| `GAME_PLAN.md` | Roadmap, toolchain findings, publication checklist |

This repository started from the
[GameSkeleton](https://github.com/hhu-adam/GameSkeleton) template.
