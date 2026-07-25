import LeanModels.Python.Surface
import LeanModels.Python.LoopTactic
import LeanModels.Python.Delab

/-!
# The Python programs of the game

Every level's subject matter is loaded here, once, from the JSON envelopes
bundled in `GameAssets/envelopes/` (copied verbatim from lean-surfaces'
`Examples/python/<name>/<name>.json`; the matching `.py` sources sit next to
them for reference).

`load_program` runs at *build* time and resolves relative paths against the
current working directory, which under `lake build` is the game root — so
always build from the repo root. Each command ingests the envelope and defines
the named constant as a literal `LeanModels.Python.Module` AST term.

NOTE (import hygiene): we import the three spec-surface modules directly, NOT
the `LeanModels.Python` umbrella — the umbrella includes `Tests`, which itself
calls `load_program` with lean-surfaces-repo-relative paths that do not exist
from the game's working directory.

The `#py_check` lines are the non-vacuity convention of the parent framework:
each envelope is run on concrete inputs at build time, so the programs the
levels reason about demonstrably execute.
-/

open LeanModels LeanModels.Python

load_program tri from "GameAssets/envelopes/tri.json"
load_program add from "GameAssets/envelopes/add.json"
load_program midpoint from "GameAssets/envelopes/midpoint.json"
load_program my_abs from "GameAssets/envelopes/my_abs.json"
load_program arith from "GameAssets/envelopes/arith.json"
load_program ag_clamp01 from "GameAssets/envelopes/ag_clamp01.json"
-- Loaded now for World 3 ("Loop World", designed in GAME_PLAN.md):
load_program sum_to from "GameAssets/envelopes/sum_to.json"

#py_check tri(4) = 10
#py_check add(2, 3) = 5
#py_check midpoint(3, -4) = -1
#py_check my_abs(-5) = 5
#py_check arith.mod(7, 0) raises .zeroDivisionError
#py_check ag_clamp01.clamp01(7) = 1
#py_check sum_to(10) = 55
