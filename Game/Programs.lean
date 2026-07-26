import LeanModels.Python.Surface
import LeanModels.Python.LoopTactic
import LeanModels.Python.VCTactic
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
-- World 3 ("Loop World"):
load_program sum_to from "GameAssets/envelopes/sum_to.json"
load_program odd_sum from "GameAssets/envelopes/odd_sum.json"
load_program gcd from "GameAssets/envelopes/gcd.json"
load_program nested_flow from "GameAssets/envelopes/nested_flow.json"

#py_check tri(4) = 10
#py_check add(2, 3) = 5
#py_check midpoint(3, -4) = -1
#py_check my_abs(-5) = 5
#py_check arith.mod(7, 0) raises .zeroDivisionError
-- The floor arc's C-vs-Python pair (cited by StraightLineWorld L3/L4):
-- truncation would give -7 // 2 = -3; Python floors to -4.
#py_check arith.floordiv(7, 2) = 3
#py_check arith.floordiv(-7, 2) = -4
#py_check ag_clamp01.clamp01(7) = 1
#py_check sum_to(10) = 55
#py_check odd_sum(7) = 49
#py_check gcd(12, 18) = 6
#py_check nested_flow.first_factor(12) = 2
#py_check nested_flow.first_factor(13) = 13
