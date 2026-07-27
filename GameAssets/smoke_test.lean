/- Smoke test for The Python Proof Game levels — NOT part of the game build.
Run from the game root with `lake env lean GameAssets/smoke_test.lean`.
Trials every World 1 / World 2 / World 3 statement with its intended proof. -/
import LeanModels.Python.Surface
import LeanModels.Python.LoopTactic
import LeanModels.Python.VCTactic
import LeanModels.Python.Delab

open LeanModels LeanModels.Python

load_program tri from "GameAssets/envelopes/tri.json"
load_program add from "GameAssets/envelopes/add.json"
load_program midpoint from "GameAssets/envelopes/midpoint.json"
load_program my_abs from "GameAssets/envelopes/my_abs.json"
load_program arith from "GameAssets/envelopes/arith.json"
load_program ag_clamp01 from "GameAssets/envelopes/ag_clamp01.json"
load_program sum_to from "GameAssets/envelopes/sum_to.json"
load_program odd_sum from "GameAssets/envelopes/odd_sum.json"
load_program gcd from "GameAssets/envelopes/gcd.json"
load_program nested_flow from "GameAssets/envelopes/nested_flow.json"

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

-- W2L1: add — plus the wave-1 framework sanity: `py_check` must REFUSE the
-- symbolic goal (free-variable guard, lean-surfaces 0ff4bb7 fix 1; before
-- that fix, kernel reduction let py_check cheese this very statement).
example (a b : PyInt) : add(a, b) ==> a + b := by
  fail_if_success py_check
  py_prove [add]

-- W2L2: midpoint, honest fdiv (step 1 of the floor arc: name the function)
theorem midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2 := by
  py_prove [midpoint]

-- The floor arc's non-vacuity pair, as the level texts cite them
#py_check arith.floordiv(7, 2) = 3
#py_check arith.floordiv(-7, 2) = -4

-- W2L3 "Floor means floor" (step 2): the ⇓ hypothesis + determinism
-- (CallsTo.typed_int_eq) pin q, then the division algorithm + grind.
-- NOTE toolkit findings: omega does NOT know Int.fdiv (opaque atom), cannot
-- multiply two variables (b * q), and skips PyInt-branded goals — grind
-- handles all three. Core v4.33 names: Int.fmod_add_fdiv_mul (there is no
-- Int.fmod_add_fdiv), Int.fmod_nonneg_of_pos, Int.fmod_lt_of_pos.
theorem floordiv_is_floor (a b q : PyInt) (hb : 0 < b)
    (hq : arith.floordiv(a, b) ⇓ q) :
    b * q ≤ a ∧ a < b * (q + 1) := by
  have hb' : b ≠ 0 := by grind
  have hrun : arith.floordiv(a, b) ==> Int.fdiv a b := by py_prove [arith, hb']
  have hqe : q = Int.fdiv a b := CallsTo.typed_int_eq hq hrun
  have hkey := Int.fmod_add_fdiv_mul a b
  have h0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg_of_pos a hb
  have h1 : Int.fmod a b < b := Int.fmod_lt_of_pos a hb
  grind

-- W2L4 "Python is not C" (step 3): the concrete run + determinism refute
-- C's truncating answer; the forced equation -3 = -4 is Int-headed, so
-- omega finishes on its home turf.
theorem python_is_not_C : ¬ (arith.floordiv(-7, 2) ==> -3) := by
  intro h
  have hrun : arith.floordiv(-7, 2) ==> -4 := by py_check
  have h34 := CallsTo.typed_int_eq h hrun
  omega

-- W2L5: the pretty `/` form, now unconditional (wave-1 fix: the former
-- `midpoint_nonneg`'s `ha`/`hb` were vacuous — the identical tactic closes
-- the stronger statement, and no unused-variable laundering is needed).
example (a b : PyInt) : midpoint(a, b) ==> (a + b) / 2 := by
  py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]

-- W2L6: branching
example (x : PyInt) : my_abs(x) ==> |x| := by py_prove [my_abs]

-- W2L7 (boss): two sequential ifs, outside py_prove's recipe. Since
-- lean-surfaces 0ff4bb7 (fix 2) that failure is CURATED — a one-paragraph
-- pointer to py_vcgen/py_simp, not a raw interpreter-state dump — so the
-- sanity check can now run inline instead of sitting in a comment:
example (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  fail_if_success py_prove [ag_clamp01]
  refine ⟨32, ?_⟩
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind

-- W2L8 (coda): the same boss shape, generated — one py_vcgen call + sweep
example (x : PyInt) : ag_clamp01.clamp01(x) ==> min 1 (max 0 x) := by
  py_vcgen [ag_clamp01]
  all_goals omega

-- W3L1: tri, clause form (the level's Template with its Holes filled).
-- SIX residuals since 0ff4bb7 (fix 4): init, exit, preserve, preserve2,
-- dec, ret — preservation splits per conjunct and same-tag duplicates are
-- numbered (the level text walks through exactly these six).
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_vcgen [tri]
    (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
    (dec := fun (total i : Int) => (n + 1 - i).toNat)
  case ret =>
    obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind

-- W3L2: tri, DELAYED mode — the player invents the invariant mid-proof
example (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_vcgen [tri]
  case inv1 => exact fun total i => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)
  case dec1 => exact fun total i => (n + 1 - i).toNat
  case ret =>
    obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind

-- W3L3: odd_sum — player-invented invariant from scratch
theorem odd_sum_total (n : PyInt) (hn : 0 ≤ n) : odd_sum(n) ==> n * n := by
  py_vcgen [odd_sum]
    (inv := fun (total k : Int) => 0 ≤ k ∧ k ≤ n ∧ total = k * k)
    (dec := fun (total k : Int) => (n - k).toNat)
  all_goals grind

-- W3L4: sum_to — the countdown shadows its own argument; theorem binds `N`
theorem sum_to_total (N : PyInt) (hN : 0 ≤ N) : sum_to(N) ==> N * (N + 1) / 2 := by
  py_vcgen [sum_to]
    (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
    (dec := fun (s n : Int) => n.toNat)
  case ret =>
    obtain rfl : n' = 0 := by omega
    grind
  all_goals grind

-- W3L5: gcd — Euclid's invariant (the level's Template with Holes filled).
-- Since 0ff4bb7 (fix 4) the twice-used preservation tag is numbered
-- (preserve/preserve2), so the case-tag route works end-to-end — the level
-- now teaches it instead of positional bullets.
theorem gcd_total (A B : PyInt) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    gcd(A, B) ==> Int.gcd A B := by
  py_vcgen [gcd]
    (inv := fun (a b : Int) => 0 ≤ a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B)
    (dec := fun (a b : Int) => b.toNat)
  case exit =>
    exact ⟨a, ⟨rfl, hx⟩, hcore.1, by rw [← hcore.2.2, hx, Int.gcd_zero_right]⟩
  case preserve => exact Int.fmod_nonneg hinv1 hinv2
  case preserve2 =>
    rw [gcd_fmod_step hinv1 hinv2]
    exact hinv3
  case dec =>
    have h1 := Int.fmod_lt_of_pos a (b := b) (by omega)
    have h2 := Int.fmod_nonneg hinv1 hinv2
    omega
  case ret => grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]

-- W3L6 (boss): nested loop + break + mid-loop return, even case —
-- five clauses (two inv/dec pairs + the break's exit2 fact), one sweep.
-- The former opening `have hn2 : (2:Int) ≤ n := hn` was vestigial (three
-- independent playtest reports): grind sees through the PyInt brand, and
-- the sweep closes all nine residuals without the rebrand.
theorem first_factor_even (n : PyInt) (hn : 2 ≤ n) (h2 : (2:Int) ∣ n) :
    nested_flow.first_factor(n) ==> 2 := by
  py_vcgen [nested_flow]
    (inv1 := fun (i : Int) => i = 2)
    (dec1 := fun (i : Int) => (n - i).toNat)
    (inv2 := fun (m : Int) => 0 ≤ m ∧ (2:Int) ∣ (n - m))
    (dec2 := fun (m : Int) => m.toNat)
    (exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m))
  all_goals grind

-- W3L6 delayed-mode sanity (0ff4bb7 fix 5): bare py_vcgen now REQUESTS the
-- break-carrying loop's exit clause as goal `exit2`, next to inv/dec — the
-- route the level's intro now advertises.
example (n : PyInt) (hn : 2 ≤ n) (h2 : (2:Int) ∣ n) :
    nested_flow.first_factor(n) ==> 2 := by
  py_vcgen [nested_flow]
  case inv1 => exact fun i => i = 2
  case dec1 => exact fun i => (n - i).toNat
  case inv2 => exact fun m => 0 ≤ m ∧ (2:Int) ∣ (n - m)
  case dec2 => exact fun m => m.toNat
  case exit2 => exact fun m => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m)
  all_goals grind

-- Non-vacuity for the new programs, as the level texts cite them
#py_check sum_to(10) = 55
#py_check odd_sum(7) = 49
#py_check gcd(12, 18) = 6
#py_check nested_flow.first_factor(12) = 2
#py_check nested_flow.first_factor(13) = 13
