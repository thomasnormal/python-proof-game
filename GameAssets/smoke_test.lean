/- Smoke test for The Python Proof Game levels — NOT part of the game build.
Run from the game root with `lake env lean GameAssets/smoke_test.lean`.
Trials every planned World 1 / World 2 statement with its intended proof. -/
import LeanModels.Python.Surface
import LeanModels.Python.LoopTactic
import LeanModels.Python.Delab

open LeanModels LeanModels.Python

load_program tri from "GameAssets/envelopes/tri.json"
load_program add from "GameAssets/envelopes/add.json"
load_program midpoint from "GameAssets/envelopes/midpoint.json"
load_program my_abs from "GameAssets/envelopes/my_abs.json"
load_program arith from "GameAssets/envelopes/arith.json"
load_program ag_clamp01 from "GameAssets/envelopes/ag_clamp01.json"

-- #py_check non-vacuity, as the levels' Introductions will cite them
#py_check tri(4) = 10
#py_check midpoint(3, -4) = -1
#py_check arith.mod(7, 0) raises .zeroDivisionError

-- W1L1: concrete loop run — `py_check` makes the kernel run the program
example : tri(4) ==> 10 := by py_check
-- NOTE: `by decide` does NOT work here — `Res`/`Val` carry no `DecidableEq`
-- instance (the repo's #py_check uses `#guard` with `BEq` instead).
-- `py_check` (fuel witness + kernel evaluation, Surface.lean) is the honest
-- concrete-run proof; it replaced the hand-rolled `refine ⟨100, ?_⟩; rfl`.

-- W1L2: concrete floor-division surprise
example : midpoint(3, -4) ==> -1 := by py_check

-- W1L3: concrete raise — py_check closes `==>!` goals too
example : arith.mod(7, 0) ==>! .zeroDivisionError := by py_check

-- W1L4 (bridge): first symbolic statement
example (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError := by
  py_prove [arith]

-- W2L1: add
example (a b : PyInt) : add(a, b) ==> a + b := by py_prove [add]

-- W2L2: midpoint, honest fdiv
theorem midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2 := by
  py_prove [midpoint]

-- W2L3: precondition level via py_corollary
set_option linter.unusedVariables false in
example (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : midpoint(a, b) ==> (a + b) / 2 := by
  py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]

-- W2L4: branching
example (x : PyInt) : my_abs(x) ==> |x| := by py_prove [my_abs]

-- W2L5 (boss): two sequential ifs, outside py_prove's recipe
example (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  refine ⟨32, ?_⟩
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind

-- Sanity: py_prove should FAIL on the boss shape (so the level genuinely needs
-- the manual toolbox). Expect this to error if uncommented:
-- example (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
--   py_prove [ag_clamp01]
