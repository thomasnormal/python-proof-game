# The Python Proof Game — plan

A [lean4game](https://github.com/leanprover-community/lean4game) that teaches
formal verification of **real Python programs** using the
[lean-surfaces](https://github.com/thomasnormal/lean-surfaces) framework
(deep-embedded Python in Lean 4, verified interpreter differentially tested
against CPython, typed spec surface: `f(a) ==> v`, `py_prove`, `py_loop`, …).

## Status

- **Built and green**: Worlds 1–3 (23 levels: 6 + 8 + 9), full `lake build`
  including `MakeGame`; gamedata generated at `.lake/gamedata/`. World 1
  ("Machine World") is **symbolic-first** since wave 3: two witness-hunting
  `∃` puzzle levels, the `py_prove` thesis moment at the world's midpoint,
  and a two-variable for-all capstone. World 2 carries the `py_vcgen` coda
  ("The machine rises") and the **floor arc** (L1–L3: name it / prove it /
  spend it). World 3 ("Loop World") is built on `py_vcgen` clause +
  delayed-goal modes. **Wave 2** (progression-study restructure, below)
  added six levels, capped every intro at ≤200 words, and made 53% of hints
  hidden; **wave 3** (witness redesign, below) traded two Machine World
  `py_check` reps for puzzle levels and absorbed `add_total` — exercise
  share now 8/23 ≈ 35% (honest recount below).
- **Designed, not built**: World 4 (RSA World, below) — next up.

## Toolchain findings (the critical reconciliation)

| Component | Version | Note |
|---|---|---|
| Game toolchain | `leanprover/lean4:v4.33.0-rc1` | matches lean-surfaces exactly |
| lean-surfaces (`lean-models`) | git `8cb98e2e28c8e6a5340a79562d1d9448a49250d1` | == public `master`; the rev that adds `py_vcgen` (VCTactic.lean, the flow-aware VC walker). Previously `60ae7c8d` (first rev with `py_check`) |
| lean4game GameServer | git tag `v4.31.0` (newest release) | **compiles cleanly under v4.33.0-rc1** |
| batteries | tag `v4.33.0-rc1` (root-level pin) | shadows GameServer's transitive `v4.31.0` require, which would not build on this toolchain |
| i18n (hhu-adam) | `v4.31.0` (via GameServer) | compiles cleanly under v4.33.0-rc1 |
| mathlib | `v4.33.0-rc1` (transitive via lean-surfaces) | **cloned but never built** — the game imports only the core-only Python lane |

Key facts discovered on the way:

1. lean4game has **no `v4.33.*` tag** (newest: `v4.31.0`; `main` is also on
   v4.31.0). GameSkeleton's lakefile derives the GameServer tag from
   `Lean.versionString`, which would request the nonexistent `v4.33.0-rc1`
   tag — the game's `lakefile.lean` hardcodes `gameServerVersion := "v4.31.0"`.
2. GameSkeleton's lakefile was written against Lake ≤ 4.23:
   `Dependency.version?` no longer exists (now `version : InputVer`) and
   `src?` is now an `Option`. Fixed in `lakefile.lean` for the v4.33 Lake API.
3. GameServer v4.31.0 + i18n v4.31.0 compile **without a single error** under
   v4.33.0-rc1, with batteries pinned to its `v4.33.0-rc1` tag (the root-level
   `require` wins over GameServer's transitive one). No code patches needed.
4. The game must **not** import the `LeanModels.Python` umbrella:
   `LeanModels.Python.Tests` executes `load_program` with
   lean-surfaces-repo-relative paths, which fail from the game's cwd. Import
   `LeanModels.Python.{Surface, LoopTactic, Delab}` directly
   (see `Game/Programs.lean`).
5. `load_program` resolves relative paths against the **current working
   directory** (the game root under `lake build`); envelopes are bundled in
   `GameAssets/envelopes/` and load fine. Always build from the repo root.
6. `decide` cannot close concrete-run goals (`Res`/`Val` have `BEq` but no
   `DecidableEq`); the honest concrete proof is a fuel witness + `rfl`
   (kernel-executes the interpreter). Since lean-surfaces `60ae7c8d` the
   framework packages exactly that as the `py_check` tactic — the tactic twin
   of `#py_check` — which World 1 now uses instead of a hand-rolled
   `refine ⟨fuel, ?_⟩; rfl`.

Fallback ladder if this pinning ever breaks (not needed today):
game on v4.31.0 + a vendored lean-surfaces trimmed to the Python lane
(core-only, drop the mathlib require) — the Python lane uses no mathlib, so
only `grind`/`omega` behavior drift matters; last resort, wait for a lean4game
toolchain bump.

## Worlds and levels

### World 1 — Machine World (built; 6 levels; wave-3 shape)

**Design principle (wave 3): concrete levels exist to ground the judgment,
not to be the world.** Two concrete runs (L1 watch, L2 predict) teach what
`==>` *means*; from L3 on, every level withholds something the player must
supply — a witness, a symbolic proof, a common answer — instead of
repeating bare `py_check`. The witness levels are predict-then-verify with
teeth: a wrong prediction doesn't get corrected by the kernel, it *stalls
the proof* (`py_check` refuses to certify a false run) until the player
recounts.

| # | Level | Statement | Proof | Introduces |
|---|---|---|---|---|
| 1 | Run it | `tri(4) ==> 10` | `py_check` | `==>`, fuel, `py_check`, programs `tri` + `midpoint` |
| 2 | The floor is not the ceiling | `midpoint(3, -4) ==> -1` | same shape | **nothing** (exercise; midpoint doc moved to L1; predict `//` on a negative sum before the kernel answers) |
| 3 | Find the input *(wave 3)* | `∃ n : PyInt, tri(n) ==> 15` (anonymous) | `refine ⟨5, ?_⟩` → `py_check` | `refine`, the `⟨…⟩` anonymous-constructor tile in its *gentle* form (a number witness; fuel donation is its later callback). A `Branch` anticipates the off-by-one `⟨4, ?_⟩` |
| 4 | Infinitely many tests, one line | `floordiv_zero (n : PyInt) : arith.floordiv(n, 0) ==>! .zeroDivisionError` | `py_prove [arith]`, player-typed | the world's thesis, mid-world: `==>!`, module `arith`, `py_prove` — and `py_check`'s on-principle refusal of free variables |
| 5 | Two programs, one answer *(wave 3)* | `∃ v : PyInt, tri(4) ==> v ∧ midpoint(13, 7) ==> v` (anonymous) | `refine ⟨10, ?_, ?_⟩ <;> py_check` | `«<;>»` (first use: sweep both conjunct runs; moved here from the W2 boss); program `add` (foreshadow) |
| 6 | Every pair of integers ever | `add_total : add(a, b) ==> a + b` | `py_prove [add]` | **nothing** (exercise: the L4 move player-driven on two binders — old W2L1, absorbed as the world capstone) |

### World 2 — Straight-Line World (built; 8 levels since wave 3)

Symbolic inputs, loop-free bodies. Wave 3 absorbed the old L1 (`add_total`)
into Machine World's capstone and renumbered the rest down one — the world
now opens directly on real content and flows straight into the floor arc.

| # | Level | Statement | Proof | Introduces |
|---|---|---|---|---|
| 1 | Say floor when you mean floor | `midpoint_spec : midpoint(a, b) ==> Int.fdiv (a + b) 2` | `py_prove [midpoint]` | the honest `Int.fdiv` statement discipline; named statement enters inventory. **Step 1 of the floor arc**: *name* the function the program computes |
| 2 | **Floor means floor** (arc step 2) | `floordiv_is_floor (a b q : PyInt) (hb : 0 < b) (hq : arith.floordiv(a, b) ⇓ q) : b * q ≤ a ∧ a < b * (q + 1)` | `have hb' : b ≠ 0 := by grind` → `have hrun : … ==> Int.fdiv a b := by py_prove [arith, hb']` → `have hqe := CallsTo.typed_int_eq hq hrun` → stage `Int.fmod_add_fdiv_mul` + `Int.fmod_nonneg_of_pos` + `Int.fmod_lt_of_pos` → `grind` | the `⇓` result-binding hypothesis (`ResultArrow` doc tile), determinism as a *player move* (`CallsTo.typed_int_eq`), the division-algorithm toolkit, `have`, `grind` (and both reasons `omega` can't: `PyInt` brand + the nonlinear `b * q`). Wave 2: stages 2–5 of the hint ladder are hidden (le_total pattern) |
| 3 | **Python is not C** (arc step 3) | `python_is_not_C : ¬ (arith.floordiv(-7, 2) ==> -3)` | `intro h` → `have hrun : … ==> -4 := by py_check` → `have h34 := CallsTo.typed_int_eq h hrun` → `omega` | negation-as-implication (`intro`), refutation via determinism, `omega` on its home turf |
| 4 | The strongest honest statement | `midpoint_div : midpoint(a, b) ==> (a + b) / 2` (unconditional) | `py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]` | preconditions-as-hypotheses, `py_corollary`, value bridging without re-execution; programs `my_abs` + `my_max` (foreshadow the fork pair) |
| 5 | Fork in the road | `my_abs_spec : my_abs(x) ==> \|x\|` | `py_prove [my_abs]` | **nothing** (exercise since wave 2; the branching *mode* is prose + the `py_prove` doc, not an item) |
| 6 | Fork, again *(wave 2)* | `my_max(a, b) ==> max a b` (anonymous) | `py_prove [my_max]` | **nothing** (exercise: second lone-`if` program from scratch — fresh envelope, extractor conventions; `omega` knows `max` natively) |
| 7 | **Boss: clamp01** | `clamp01_total : ag_clamp01.clamp01(x) ==> max 0 (min 1 x)` | `refine ⟨32, ?_⟩; by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;> py_simp [callFunction, ag_clamp01, h1, h2] <;> grind` | the documented boundary of `py_prove`; `py_simp`, `by_cases` — since wave 3, `refine`/`⟨…⟩`/`<;>` are *Machine World callbacks* (“the same witness move — this time the witness is fuel”), not new items. Wave 2: “toughest level yet” warning; the one-breath chain is a hidden hint |
| 8 | **Coda: the machine rises** | `clamp01_machine : ag_clamp01.clamp01(x) ==> min 1 (max 0 x)` | `py_vcgen [ag_clamp01]` + `all_goals omega` | `py_vcgen` (the VC walker: the whole boss fight, generated), `all_goals`; the walker needs **no fuel**, which is why it survives loops |

(Verified during design: `py_prove [ag_clamp01]` genuinely fails on the boss —
the level teaches a real boundary, not a staged one. The coda states the
clamp with `min`/`max` nested the *other* way so its statement isn't literally
the boss's. Verified for the floor arc: `grind` alone — without the three
staged division-algorithm facts — does NOT close `floordiv_is_floor`, and
`py_prove` alone cannot either; the level's content is real. Wave-2
verified: `py_prove [my_max]` closes the `max a b` fork — its `split; omega`
recipe knows `max` as natively as `|·|`.)

### World 3 — Loop World (built; 9 levels)

`while` loops on `py_vcgen` (VCTactic.lean, lean-surfaces `8cb98e2e`):
clause mode `(inv := …) (dec := …)`, and — the world's central mechanic —
**delayed-goal mode**: `py_vcgen [prog]` bare leaves `case inv1 ⊢ Int → … →
Prop` and `case dec1 ⊢ Int → … → Nat` goals; assigning them (with `exact
fun … => …`) instantiates every downstream residual, so wrong invariants
produce *residual goals as feedback*. Residual tags: `init`, `preserve`,
`dec`, `exit` (an ∃-shaped repack of invariant + negated test at the exit
point — `grind` food), `ret`.

| # | Level | Statement | Proof | Introduces |
|---|---|---|---|---|
| 1 | Anatomy of a loop proof | `tri_total (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2` | full clause-mode proof as a visible `Template`; player fills two `grind` Holes (`case ret` finish + `all_goals`) | invariant/measure as clauses, the residual tags, `case`, `obtain`/`rfl`, `Int`; since wave 3 also the hidden `Template` (the first templated level — Machine World's bridge Template is gone). Wave 2: intro dieted 521→200 words — the tag glossary lives on the `py_vcgen` doc tile |
| 2 | **Invent the invariant** (the heart) | same claim, anonymous | `py_vcgen [tri]` bare → player answers `inv1`/`dec1` with `exact fun total i => …`, then closes the residuals | delayed-goal mode; `exact`; the two honest failure modes (below, kept undiluted through the wave-2 prose diet); programs `double_sum` + `odd_sum` (foreshadow) |
| 3 | Invent it again, doubled *(wave 2)* | `double_sum(n) ==> n * (n - 1)` for `n ≥ 0` (anonymous) | delayed mode: `py_vcgen [double_sum]` bare, `inv1 := 0 ≤ k ∧ k ≤ n ∧ total = k * (k - 1)`, `dec1 := (n - k).toNat`, `all_goals grind` | **nothing** (exercise: the game's central skill, second rep on a near-isomorphic fresh loop; product-form books, no `ret` surgery) |
| 4 | The sum of odd numbers | `odd_sum_total (hn : 0 ≤ n) : odd_sum(n) ==> n * n` | clauses from scratch (`total = k * k` + range; `(n - k).toNat`), `all_goals grind` sweeps everything incl. `ret` | **nothing** (exercise since wave 2: `odd_sum` doc moved to L2) |
| 5 | The shadowed variable | `sum_to_total (N) (hN : 0 ≤ N) : sum_to(N) ==> N * (N + 1) / 2` | clauses with binders `(s n : Int)`; `case ret => obtain rfl : n' = 0` | the shadowing rule: the loop mutates Python's `n`, so the *theorem* binds the initial value as capital `N`; program `steps` (foreshadow) |
| 6 | The walk home *(wave 2)* | `steps(N) ==> \|N\|` — **no hypothesis** (anonymous) | `py_vcgen [steps] (inv := 0 ≤ count ∧ count + \|n\| = \|N\|) (dec := n.natAbs)`, `all_goals grind` | **nothing** (exercise combiner: branch inside the loop body + shadowing + `\|·\|` reuse; `n.natAbs` because `n.toNat` dies on the negative side) |
| 7 | Euclid's invariant | `gcd_total (hA : 0 ≤ A) (hB : 0 ≤ B) : gcd(A, B) ==> Int.gcd A B` | Template: clauses + residuals by `case` tag (exit-packaging given; Holes for `Int.fmod_nonneg`, `gcd_fmod_step` rewrite, the `Int.fmod_lt_of_pos` measure argument, and the `grind [gcd_zero_right, natAbs_of_nonneg]` payout) | an invariant that is a *theorem* (gcd-preservation); the `Int.fmod` spec-side library as `NewTheorem`s; `rw` |
| 8 | Cool-down: gcd doesn't care *(wave 2)* | `gcd_comm (hA) (hB) : gcd(A, B) ==> Int.gcd B A` | `rw [Int.gcd_comm]` → `py_corollary [gcd_total]` — two lines, zero interpreter | `Int.gcd_comm`; program `nested_flow` (foreshadow the boss's lair). The P3 relief valve after the hardest manual level *and* the P6 lemma-reuse beat: `gcd_total` pays its first dividend |
| 9 | **Boss: the nested machine** | `first_factor_even (hn : 2 ≤ n) (h2 : 2 ∣ n) : nested_flow.first_factor(n) ==> 2` | `py_vcgen [nested_flow]` with **five clauses** (`inv1`/`dec1`, `inv2`/`dec2`, `exit2`); `all_goals grind` | **nothing** (wave 2: `nested_flow` doc moved to L8, so the boss spends difficulty, not novelty). “Toughest fight in the game” warning; full call + sweep are hidden hints; numbered clauses, the `exit2` a `break` requires, the unreachability invariant `i = 2` |

Boss scoping, honestly: the gallery's unconditional
`first_factor_total` (`==> n.toNat.minFac`) needs mathlib (`minFac`
machinery) which the game deliberately never builds — so the boss proves the
**even case** (`2 ∣ n → returns 2`), which exercises the *full* control
shape (nested `while`, `break`-in-`if`, mid-loop `return`, `exit2` clause —
"the proof `py_loop` could never do") while keeping every residual
elementary (`grind` sweeps all nine). The conclusion points at the gallery
proof as the same clause skeleton with number theory in the residuals.

L2's wrong-invariant pedagogy, as *actually verified* on this toolchain:

* **too weak** (books without range conjuncts): `init`/`preserve`/`dec`/
  `exit` all close; the `ret` goal is left with only `hcont : n < i'` and is
  honestly unprovable — `grind` fails with a countermodel-flavored
  diagnostic. This is the level's central lesson (true ≠ useful).
* **wrong measure** (`i.toNat` for a counting-up loop): the `dec` residual
  comes back `(i + 1).toNat < i.toNat` — visibly false.
* The planned third failure ("missing the `2 * total` form → `grind` stalls
  on division") is **not real on v4.33**: grind's integer-division theory
  closes the `total = i * (i - 1) / 2` form end-to-end. The level keeps the
  multiplication-free house style but tells the truth about why (it matters
  on later programs, e.g. the `gcd` residuals, not on `tri`).

### World 4 — RSA World (designed, not built — NEXT)

The framework's real-world capstone, `Examples/python/rsa_inverse`:
`extended_gcd` + `inverse` from **python-rsa 4.9.1, byte-verbatim**.

1. **Meet the code** — concrete runs of `extended_gcd`, incl.
   `extended_gcd(3, 7) = (1, 5, 1)` — and the sting: `5·3 + 1·7 = 22 ≠ 1`,
   the textbook Bézout identity is *false* for the shipped code.
2. **Unreachable code needs no semantics** — `inverse` contains
   `raise NotRelativePrimeError` (out of tier!); prove a coprime instance
   runs anyway: under `gcd = 1` symbolic execution never enters the branch.
3. **The seven-variable invariant** (multi-level, Template/Hole staged):
   the `egcdInv` invariant — gcd preservation, *modular* Bézout, the
   sign-alternation block — one conjunct-hole per level.
4. **Boss: `inverse_spec`** — total correctness of the shipped modular
   inverse, plus `inverse_no_raise`: the exception provably cannot fire.

This world is the payoff narrative: "the docstring's invariant is subtly
wrong, the proof found the honest one, and testing could never see the
difference."

## Wave 2 — progression-study restructure (2026-07)

*(Historical snapshot: level counts and W1/W2 numbering below predate wave 3
— the current shape is the world tables above and the wave-3 section
next.)*

Applied the comparative-study recommendations (R1/R2/R4/R7 of
`/tmp/game-study/progression-report.md`; NNG4/Robo/STG4/Logic corpus). The
game went from 18 levels (6 of them one world) to **24 levels (6 + 9 + 9)**.

**R1 — exercise share: 10/24 = 41.7%** (was 0/16 = 0%; genre floor ≈ 42%,
NNG 66%). Zero-new-item levels, gamedata-verified: W1L2, W1L3, W1L5, W2L1,
W2L6, W2L7, W3L3, W3L4, W3L6, W3L9. Five are new reps (W1L3 predict-the-floor,
W1L5 second crash, W2L7 `my_max`, W3L3 `double_sum` delayed-mode invariant
rep, W3L6 `steps` loop+branch combiner); four are conversions by
**front-loading subject-matter docs** (program `DefinitionDoc`s move to the
preceding intro level whose conclusion foreshadows them — `midpoint`→W1L1,
`add`→W1L6, `my_abs`/`my_max`→W2L5, `odd_sum`→W3L2, `steps`→W3L5,
`nested_flow`→W3L8), making the boss itself a zero-novelty pure-difficulty
level, NNG-style. New items/level: 2.61 → **2.12** (51 items / 24 levels;
the tool-heavy intro levels are unchanged — the lever was share, not
totals).

**R2 — cool-down + reuse**: W3L8 `gcd_comm` (`rw [Int.gcd_comm]` +
`py_corollary [gcd_total]`) is the relief valve after Euclid *and* the
second `py_corollary` rep *and* the first dividend on `gcd_total`
(player-proved-statement reuse instances: 1 → 2 — `midpoint_spec` at W2L5,
now `gcd_total` at W3L8; the `Int.fmod` toolkit additionally recurs across
W2L3/W3L7). Loop World's
proof-line curve is now a sawtooth with plateaus:
[t, 7, 4, 4, 7, 4, 11, 2, 8] instead of [6, 7, 4, 7, 11, 8].

**R4 — prose diet**: every intro ≤ 200 words (script-counted, code blocks
included). Worst offenders before → after: W3L1 521→200, W3L9 456→200,
W2L3 361→199, W3L7 344→199, W3L2 340→200 (the two wrong-guess catalogs kept
undiluted — the cut was the surrounding exposition), W2L8 326→196,
W2L5 273→188, W3L5 255→199, W2L4 239→178, W3L4 229→156, W2L2 206→186.
Reference material (residual-tag glossary, tactic recaps) lives in the
`py_vcgen`/`case`/`obtain` doc tiles, which the level texts now point at.

**R7 — hint rebalance**: 60 hints, 32 hidden = **53% hidden** (NNG 46%;
was 0%). Pattern: visible hint = orientation, hidden hint = the answer's
shape; the W2L3 ladder is fully staged with strict+hidden stages 2–5
(le_total pattern). Both bosses open with a “toughest yet” warning and
carry their full solves only in hidden hints; every exercise level has ≥ 1
hidden hint (they have no new-item crutch).

Deliberately *not* done in this wave: R3 (`grind` confiscation — still
vigilance-only), R5 (Gauntlet World + branching the map), R6 beyond the
`gcd_comm` instance. R5 is the next structural step and would lift the
exercise share further.

## Wave 3 — witness-hunting Machine World (2026-07)

The wave-2 Machine World fixed the exercise share at a cost: three of its
six levels were *bare `py_check` reps* — the same one-word move four times
before anything changed. Wave 3 redesigns the early game around
**witness-hunting as the puzzle mechanic** and pulls the game's thesis
(you cannot run infinitely many tests; a proof can) into Machine World
itself. The design principle is stated with the World 1 table above:
*concrete levels exist to ground the judgment, not to be the world.*

The moves, concretely:

* **W1L3 “Find the input”** (was “Called it”, a `py_check` rep):
  `∃ n : PyInt, tri(n) ==> 15`, solved `refine ⟨5, ?_⟩` → `py_check`.
  Introduces `refine` and the `⟨…⟩` tile in its *gentle* form (a number
  witness) — the doc now leads with that and keeps fuel donation as the
  later callback. A `Branch` anticipates the off-by-one `⟨4, ?_⟩` and the
  smoke test `fail_if_success`-guards it.
* **W1L4 “Infinitely many tests, one line”** (replaces the concrete
  `mod(7, 0)` crash intro): `floordiv_zero (n : PyInt) :
  arith.floordiv(n, 0) ==>! .zeroDivisionError`, solved `py_prove [arith]`
  — *player-typed*; the old bridge's visible-`Template` crutch is dropped.
  `==>!` and `py_prove` arrive together; `py_check`'s free-variable refusal
  is the level beat (smoke-guarded by `fail_if_success py_check`).
* **W1L5 “Two programs, one answer”** (was the crash-encore rep):
  `∃ v : PyInt, tri(4) ==> v ∧ midpoint(13, 7) ==> v`, solved
  `refine ⟨10, ?_, ?_⟩ <;> py_check`. Introduces `«<;>»` (moved from the
  W2 boss); `⟨…⟩` flattens `∃` + `∧` in one stroke.
* **W1L6 “Every pair of integers ever”**: `add_total` by `py_prove [add]`
  — old W2L1, absorbed as the world capstone; still a zero-new-item
  exercise (`add`'s doc front-loaded to W1L5's conclusion).
* **W2 renumbered 9 → 8**, no backfill: the world now opens on real
  content (`midpoint_spec` straight into the floor arc), and padding it
  back to 9 would re-create exactly the kind of rep wave 3 removes.
* **Inventory dedupe**: the W2 boss no longer introduces `refine`, `«<;>»`,
  or the `⟨…⟩` tile — its prose calls back (“the same witness move from
  Machine World — this time the witness is *fuel*”). The hidden `Template`
  moved from the old W1L6 bridge to W3L1, the first remaining templated
  level.

**Exercise-share recount (honest).** Zero-new-item levels are now W1L2,
W1L6, W2L5, W2L6, W3L3, W3L4, W3L6, W3L9 = **8/23 ≈ 35%** (was 10/24 ≈
42%). Two reps became item-introducing puzzle levels; one exercise
(`add_total`) changed worlds but stayed an exercise. The drop is deliberate
and uncompensated: the traded reps were the least engaging levels in the
game, and the witness levels keep the practice *feel* — each introduces one
tactic and spends the rest of its length on the player's own arithmetic.
The item total is unchanged (wave 3 moved introduction points, it minted
nothing), so items/level ticks up slightly: 51 / 23 ≈ 2.2.

**Cumulative inventory, rebuilt and re-verified** — every intended solution
(the smoke-test proofs) uses only items unlocked at or before its level;
moving `refine`/`«<;>»`/`py_prove` *earlier* is the safe direction, and
`MakeGame` (which errors on used-before-introduced items) is the second
checker:

| Level | Introduces (New\*) | Solution uses (cumulative check) |
|---|---|---|
| W1L1 | `py_check`; `==>`, `tri`, `midpoint` | `py_check` ✓ |
| W1L2 | — | `py_check` ✓ |
| W1L3 | `refine`; `⟨…⟩` | `refine` L3, `py_check` L1 ✓ |
| W1L4 | `py_prove`; `==>!`, `arith` | `py_prove`+`arith` L4 ✓ |
| W1L5 | `«<;>»`; `add` | `refine` L3, `<;>` L5, `py_check` L1 ✓ |
| W1L6 | — | `py_prove` L4, `add` L5 ✓ |
| W2L1 | `Int.fdiv` | `py_prove` W1L4, `midpoint` W1L1 ✓ |
| W2L2 | `have`, `grind`; `typed_int_eq`, `fmod_add_fdiv_mul`, `fmod_nonneg_of_pos`, `fmod_lt_of_pos`; `⇓`, `Int.fmod` | all introduced here + `py_prove` W1L4, `arith` W1L4 ✓ |
| W2L3 | `intro`, `omega` | `intro`+`omega` L3, `have` W2L2, `py_check` W1L1, `typed_int_eq` W2L2 ✓ |
| W2L4 | `py_corollary`; `fdiv_eq_ediv_of_nonneg`; `my_abs`, `my_max` | `py_corollary` L4, `midpoint_spec` (player-proved W2L1), `fdiv_eq_ediv_of_nonneg` L4 ✓ |
| W2L5 | — | `py_prove` W1L4, `my_abs` W2L4 ✓ |
| W2L6 | — | `py_prove` W1L4, `my_max` W2L4 ✓ |
| W2L7 | `py_simp`, `by_cases`; `ag_clamp01`, `callFunction` | `refine` **W1L3**, `<;>` **W1L5**, `grind` W2L2, `by_cases`/`py_simp`/`ag_clamp01`/`callFunction` L7 ✓ |
| W2L8 | `py_vcgen`, `all_goals` | `py_vcgen`+`all_goals` L8, `ag_clamp01` W2L7, `omega` W2L3 ✓ |
| W3L1 | `case`, `obtain`, `rfl` (+thm); hidden `Hole`+`Template`; `Int` | `py_vcgen` W2L8, `tri` W1L1, rest L1 ✓ |
| W3L2 | `exact`; `double_sum`, `odd_sum` | `exact` L2, `py_vcgen`/`case`/`omega`/`grind` earlier ✓ |
| W3L3 | — | `double_sum` W3L2, delayed-mode kit W3L2 ✓ |
| W3L4 | — | `odd_sum` W3L2, clause kit W3L1 ✓ |
| W3L5 | `sum_to`, `steps` | `sum_to` L5, `obtain rfl` W3L1 ✓ |
| W3L6 | — | `steps` W3L5 ✓ |
| W3L7 | `rw`; `gcd_fmod_step`, `Int.fmod_nonneg`, `Int.gcd_zero_right`, `Int.natAbs_of_nonneg`; `gcd`, `Int.gcd` | all here + `have` W2L2, `exact` W3L2, `case` W3L1 ✓ |
| W3L8 | `Int.gcd_comm`; `nested_flow` | `rw` W3L7, `py_corollary` W2L4, `gcd_total` (player-proved W3L7) ✓ |
| W3L9 | — | `py_vcgen` clauses, `nested_flow` W3L8, `grind` W2L2 ✓ |

## Framework friction log (lean4game × lean-surfaces)

Things worth knowing when extending the game:

1. **Atom-based tactic policing.** GameServer scans every alphabetic atom in
   the player's proof; anything not whitelisted or registered errors at
   difficulty 2. All tactics players type must be `NewTactic`-registered
   (incl. `refine`); theorems used as idents (`midpoint_spec`,
   `Int.fdiv_eq_ediv_of_nonneg`) must be `NewTheorem`-registered. *Program
   constants* (`tri`, `arith`, …) and defs (`callFunction`) resolve as
   non-theorems and pass the runtime check, but `MakeGame` still wants them
   introduced — registering them as `NewDefinition` with the Python source in
   the `DefinitionDoc` turned out to be a pedagogical win, not a workaround.
2. **`Template` counts as a used tactic** in the sample proof; silence the
   MakeGame warning with `NewHiddenTactic Template` in that level.
3. **TheoremDoc placement quirk**: a named `Statement`'s `TheoremDoc` must be
   in the *same file*, above the Statement.
4. **The umbrella-import trap** (`LeanModels.Python.Tests` runs
   `load_program` with repo-relative paths) — import surface modules
   directly; see `Game/Programs.lean`.
5. **Delaborators carry over.** Goals render in surface notation
   (`tri(4) ==> 10`) in the game with zero configuration — Delab.lean's
   delaborators ride along with the import, and GameServer replays the level
   file's `open` scope for the player's session.
6. **Hints & goal size**: after committing fuel (`refine ⟨32, ?_⟩`) the goal shows the folded
   constant (`callFunction tri "tri" …`) — compact and honest. But any tactic
   that unfolds the program constant (e.g. a failing `py_simp`) dumps the
   full AST literal into the goal view. Level texts warn players to lean on
   the provided recipes.
7. **No `DecidableEq` on `Res`/`Val`** — `decide` is not an option for
   concrete runs. *Discovery resolved upstream:* the game build's workaround
   (`refine ⟨fuel, ?_⟩; rfl` by hand) fed back into the framework, which
   gained the `py_check` tactic (lean-surfaces `60ae7c8d`, Surface.lean) —
   fuel witness + kernel `rfl` for both `==>` and `==>!` concrete goals; the
   game now teaches that instead. A `DecidableEq` affordance on `Res`/`Val`
   (so `decide` also works) remains queued upstream.
8. **The `(inv := …)` named-argument risk is a non-issue** (the flagged W3
   risk, tested first thing): `py_vcgen`'s clause labels are *idents* in its
   grammar (`pyVcgenClause := " (" ident " := " term ")"`), not atoms — and
   both checkers (build-time `collectUsedInventory`, runtime
   `findForbiddenTactics`) police only alphabetic **atoms** (as tactics) and
   idents that resolve to **global theorems**. `inv`/`dec`/`inv2`/`exit2`
   don't resolve to anything, so they're invisible. No `ALLOWED_KEYWORDS`
   change, no hidden-inventory hack. (This also covers `case inv1`/`case
   ret`: the case tags are unresolvable idents.)
9. **Idents in sample proofs that DO resolve must be introduced.** `Int` (in
   every `fun (total i : Int) => …` clause) resolves to a definition →
   `NewDefinition Int` (LoopWorld L1, with a doc that earns its tile);
   `rfl` inside `obtain rfl : …` patterns resolves to the *theorem* `rfl` →
   `NewTheorem rfl` (L1) besides `NewTactic rfl`. Dot-notation projections
   (`.toNat`) never resolve — postfix forms are checker-friendly.
10. **`Hole` counts as a used tactic** exactly like `Template` (friction #2)
    — `NewHiddenTactic Hole` in the first templated LoopWorld level.
11. **`Hole` wraps tactics only, not terms** — you cannot hole out a single
    clause inside a `py_vcgen` call, so "player supplies just the invariant"
    is *not* a Template shape. Delayed-goal mode is the right tool for that
    anyway (and it's better pedagogy: wrong guesses produce residuals as
    feedback instead of a parse error).
12. **v4.33 `grind` is stronger than the W3 design assumed.** It closes the
    `total = i * (i - 1) / 2` division-form invariant end-to-end (the
    planned "grind stalls on division" failure mode is not real on this
    toolchain — L2 teaches the two failure modes that *are* real: a too-weak
    invariant leaves an unprovable `ret`, a non-decreasing measure leaves a
    visibly false `dec`). It also sweeps all nine residuals of the boss's
    even case, including the ∃-shaped `exit` repack goals. What it still
    cannot do: the `gcd` residuals over `Int.fmod` (even given the right
    lemmas as grind parameters) — hence L5's bullet-by-bullet proof, which
    is the better level for it.
13. **`py_vcgen` must be imported explicitly** — `Game/Programs.lean` now
    imports `LeanModels.Python.VCTactic` alongside Surface/LoopTactic/Delab
    (it is not reachable from the other three; symptom: `unknown tactic`).
14. **`lake update` now runs mathlib's `cache get` post-update hook**
    (~30–60 min on a cold network) even though the game never builds
    mathlib. Harmless, but budget for it when bumping the pin.
15. **`omega` does not know `Int.fdiv`/`Int.fmod`** — not even with literal
    divisors (`Int.fdiv a 2` is an opaque atom to it). It atomizes what it
    doesn't understand, but without commutativity: `a.fdiv b * b` and
    `b * a.fdiv b` are *different* atoms, so even the division-algorithm
    hypotheses don't rescue it when the goal is oriented the other way. And
    a product of two variables (`b * q`) is outside its language entirely.
    v4.33 `grind` (cutsat + ring) closes the floor characterization from
    `Int.fmod_add_fdiv_mul` + the two `fmod` range facts — but NOT without
    them (verified: bare `grind` fails on `floordiv_is_floor` even though
    its normalizer internally relates `fdiv` to `ediv`).
16. **The `PyInt` brand blinds `omega` to *goals*, not just `by_cases`
    hypotheses** (extends friction 1/№ 9 of the boss design): `b ≠ 0` with
    `b : PyInt` is invisible even when every hypothesis is Int-headed, and
    rebranding hypotheses does not help when the *goal* is branded — even
    `(0 : PyInt) < 10` defeats it. `grind` is the standard discharge for
    brand-headed side goals (`have hb' : b ≠ 0 := by grind`).
17. **Core v4.33 names for the division algorithm**: there is no
    `Int.fmod_add_fdiv` — the reassembly lemma is `Int.fmod_add_fdiv_mul`
    (`a.fmod b + a.fdiv b * b = a`); the dividend-sign-free remainder bound
    is `Int.fmod_nonneg_of_pos` (`Int.fmod_nonneg` needs both operands
    nonnegative).
18. **Introduce-once discipline for shared atoms.** Moving `have`, `grind`,
    `omega`, and `Int.fmod_lt_of_pos` into the floor arc (SLW L3/L4) meant
    *removing* them from the later levels that used to introduce them
    (Clamp01 boss, LoopWorld gcd) — each atom is registered by exactly one
    `New*` command, at first use. Also: `DefinitionDoc` names need not
    resolve to declarations, which is how the `⇓` hypothesis form gets its
    own inventory tile (`DefinitionDoc ResultArrow as "⇓"`).
19. **Staged hints in a fixed-goal proof need `(strict := true)`.** GameServer
    hints match hypotheses as well as the goal, but non-strict hints fire in
    any context that *contains* the hint's context — in a `have`-staged proof
    whose goal never changes, every earlier hint would stack up at every
    later step. Strict hints pin each message to exactly its stage.
    (`(strict := true) (hidden := true)` combine fine — wave 2 uses the pair
    for the le_total-style ladders.)
20. **`py_corollary` cannot apply a permutative rewrite under the total
    theorem's binders.** `py_corollary [gcd_total, Int.gcd_comm]` fails: the
    fallback normalizes `gcd_total` with `simp only […, Int.gcd_comm]`, and
    simp's term ordering refuses to reorient `Int.gcd A B` under the
    universally quantified `ht`. The honest route rewrites the *goal's*
    value first — `rw [Int.gcd_comm]; py_corollary [gcd_total]` — which is
    better pedagogy anyway (bridge by mathematics, then collect). Verified
    before the W3L8 level was written.
21. **Pure-code hint texts collide in i18n.** Hidden hints that consist of
    a single code span (`` `py_check` ``) reduce to identical msgids
    (`§0.`), and the build warns about duplicates across files. Harmless
    for an en-only game; if translations ever matter, give each such hint a
    word of prose.
22. **Exercise levels vs. the introduce-before-use rule.** `MakeGame` wants
    program constants introduced at or before first use (friction 1), but a
    zero-new-item exercise level may not carry `NewDefinition`. Resolution:
    front-load the program's doc onto the preceding intro level and spend a
    sentence of its conclusion foreshadowing (“`double_sum` just landed in
    your inventory”) — which is also the genre-correct move (worlds
    front-load tools, back-load practice). Named `Statement`s do **not**
    count as new items in gamedata, so exercise levels may still name and
    bank their theorems.
23. **`∃` binders over surface calls need an explicit `: PyInt`.** In
    `∃ n, tri(n) ==> 15` the argument elaborates as `ToVal.toVal n`, and
    with the binder type a metavariable the `ToVal` instance problem is
    *stuck* — statements must be written `∃ n : PyInt, tri(n) ==> 15`. The
    default pretty-printer then *hides* the binder type, so the player's
    goal view reads `∃ n, tri(n) ==> 15` (clean), while the gamedata
    `descrFormat` keeps the source-form ascription
    (`example : ∃ n : PyInt, tri(n) ==> 15 := by`) — acceptable, arguably
    clearer. After `refine ⟨5, ?_⟩` the witness substitutes and the goal is
    a fully concrete `tri(5) ==> 15`, which passes `py_check`'s
    free-variable guard (a `PyInt` literal has no fvars).
24. **Wrong witnesses die honestly.** After `refine ⟨4, ?_⟩` the goal is
    `tri(4) ==> 15`; `py_check`'s kernel run lands on `10 ≠ 15` and the
    tactic *fails* with its standard message instead of closing anything —
    so a witness level cannot be lucked through. The smoke test
    `fail_if_success`-guards both wrong-witness paths (W1L3 `⟨4, ?_⟩`,
    W1L5 `⟨11, …⟩`), and W1L3 carries a `Branch` that anticipates the
    natural off-by-one with a curated hint.
25. **The `have`-without-ascription `ToVal` trap is confirmed off-path,
    low-risk** (playtest round 3, bug-hunter). The same stuck-metavariable
    failure mode as friction #23 (`ToVal.toVal` cannot resolve without a
    binder type) could in principle bite a bare `have h := …` over a
    surface call in a Machine World `∃` goal — but `have` is not unlocked
    until `NewTactic «have»` at Straight-Line World L2
    (`L02_FloorMeansFloor.lean`); it is unavailable to the runtime checker
    anywhere in Machine World. Probed directly: the only way to even attempt
    it there is **post-unlock backtracking** — finish past SLW L2, then
    replay an earlier Machine World level — which is off the mainline path.
    No fix applied; noted so a future pass doesn't rediscover it as new.

## One-tactic levels audit

Deliverable for the post-playtest fix wave: every level whose *intended*
solution is exactly one tactic call, each with a one-line "use it" follow-up
suggestion (the floor arc is the template: a one-shot spec level becomes the
*setup* for levels that USE the proved theorem). Level ids updated to the
wave-3 numbering; wave 3 addressed the one-tactic *monotony* head-on — the
old W1 reps are now witness levels whose solutions are inherently two-step
(`refine ⟨w, ?_⟩` plus a closer), so they drop out of this table.

| Level | One-tactic solution | "Use it" follow-up suggestion |
|---|---|---|
| W1L1 Run it (`tri(4) ==> 10`) | `py_check` | **Partially resolved by wave 3**: the run's value is now *spent* twice (W1L3 counts on from it; W1L5 reuses it as a conjunct). A refutation sequel (`¬ (tri(4) ==> 11)` via `CallsTo.typed_int_eq`) remains open. |
| W1L2 The floor is not the ceiling (`midpoint(3, -4) ==> -1`) | `py_check` | Partially addressed by W2L3 (the C-vs-Python sting on `floordiv`); a direct refutation sequel (`¬ (midpoint(3, -4) ==> 0)`) remains open. |
| W1L4 Infinitely many tests, one line (`floordiv_zero`) | `py_prove [arith]` (player-typed since wave 3) | Spend the ∀: instantiate `floordiv_zero` at `10^100` where `py_check`-style evaluation is hopeless — `exact floordiv_zero (10^100)` teaches theorem-application-beats-re-execution. |
| W1L6 Every pair of integers ever (`add_total`) | `py_prove [add]` | Derive `add(a, a) ==> 2 * a` by `py_corollary [add_total]` value-rewriting — first taste of use-don't-rerun *before* the midpoint corollary level. |
| W2L1 Say floor… (`midpoint_spec`) | `py_prove [midpoint]` | **Resolved**: step 1 of the floor arc; its name is spent by W2L4 (`py_corollary`) and its discipline by W2L2/W2L3. |
| W2L4 The strongest honest statement (`midpoint_div`) | `py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]` | Use the corollary on a concrete pair without running: `midpoint(6, 8) ==> 7` by `py_corollary [midpoint_div]` — the pretty form pays out numbers. |
| W2L5 Fork in the road (`my_abs_spec`) | `py_prove [my_abs]` | Relational use: `my_abs(x) ⇓ r → 0 ≤ r` via `CallsTo.typed_int_eq` + `omega`. |
| W2L6 Fork, again (`my_max(a, b) ==> max a b`) | `py_prove [my_max]` | Deliberate rep — the traced `a = b` boundary case is the varied question. |

Not listed: W1L3/W1L5 (witness levels — two-step by construction); W2L8
(coda) and W3L4 are two calls (`py_vcgen` + a sweep), and the invented
invariant is real content; W3L8 (`gcd_comm`) is two calls by design — the
cool-down; everything else is multi-step.

## Publication checklist (per lean4game docs)

- [x] Public GitHub repository `thomasnormal/python-proof-game`, pushed.
- [x] Game metadata in `Game.lean`: `Title`, `Introduction`, `Info`,
      `Languages "en"`, `CaptionShort`, `CaptionLong` (all set;
      `Prerequisites`/`CoverImage` optional — a cover image at ≤ ~500×200 px
      under `images/` is the one nice-to-have still missing).
- [x] Dependency form: the lakefile already uses the **git** dependency on
      `https://github.com/thomasnormal/lean-surfaces` pinned to rev
      `8cb98e2e…` (no path deps anywhere), so the repo is publication-ready
      as-is. If you iterate against a local checkout meanwhile, switch the
      `require` to `from "/path/to/lean_models"` and back before pushing.
- [ ] Ensure the GitHub Actions workflow from GameSkeleton
      (`.github/workflows/build.yml`) runs green — it builds the game and
      uploads the gamedata artifact the server imports. Check the green
      checkmark on the repo start page / Actions tab.
- [ ] Trigger the import: `https://adam.math.hhu.de/import/trigger/{USER}/{REPO}`
      (white screen streaming progress until "Done.").
- [ ] Play it at `https://adam.math.hhu.de/#/g/{USER}/{REPO}`.
- [ ] Repeat push + trigger for updates.
- [ ] For a listing on the landing page: ask the server maintainers
      (Jon, on the leanprover Zulip).
- Watch item for CI: the GitHub action must use the game's toolchain
  (v4.33.0-rc1) and will clone mathlib (~1 GB) without building it; if the
  runner is tight on disk, prune `.lake/packages/mathlib/.git` in a
  post-checkout step.

## Local development

```sh
lake update          # resolve deps (manifest is committed; usually not needed)
lake build           # builds everything + MakeGame checks + .lake/gamedata
lake env lean GameAssets/smoke_test.lean   # fast re-check of all level proofs
```

To play in a browser: either open the folder in VSCode with the lean4game
devcontainer, or clone `lean4game` next to this repo, `npm install`,
`npm start`, then visit `http://localhost:3000/#/g/local/python-proof-game`
(see lean4game's `doc/running_locally.md`).
