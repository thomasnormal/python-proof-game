# The Python Proof Game — plan

A [lean4game](https://github.com/leanprover-community/lean4game) that teaches
formal verification of **real Python programs** using the
[lean-surfaces](https://github.com/thomasnormal/lean-surfaces) framework
(deep-embedded Python in Lean 4, verified interpreter differentially tested
against CPython, typed spec surface: `f(a) ==> v`, `py_prove`, `py_loop`, …).

## Status

- **Built and green**: Worlds 1–3 (16 levels: 4 + 6 + 6), full `lake build`
  including `MakeGame`; gamedata generated at `.lake/gamedata/`. World 2
  gained the `py_vcgen` coda (L6 "The machine rises"); World 3 ("Loop
  World") is built on `py_vcgen` clause + delayed-goal modes.
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

### World 1 — Machine World (built)

Concrete runs; the machine computes inside the proof.

| # | Level | Statement | Proof | Introduces |
|---|---|---|---|---|
| 1 | Run it | `tri(4) ==> 10` | `py_check` | `==>`, fuel, `py_check` (make Lean actually run the program), program `tri` |
| 2 | The floor is not the ceiling | `midpoint(3, -4) ==> -1` | same shape | floor division, concretely |
| 3 | It crashes. Prove it. | `arith.mod(7, 0) ==>! .zeroDivisionError` | same shape | `==>!`, exceptions as specified behavior; `py_check` closes both concrete shapes |
| 4 | The bridge | `floordiv_zero (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError` | `py_prove [arith]`, **given as a visible `Template`** | first symbolic statement, `py_prove` |

### World 2 — Straight-Line World (built)

Symbolic inputs, loop-free bodies.

| # | Level | Statement | Proof | Introduces |
|---|---|---|---|---|
| 1 | add, for all | `add_total : add(a, b) ==> a + b` | `py_prove [add]` | player-driven symbolic execution |
| 2 | Say floor when you mean floor | `midpoint_spec : midpoint(a, b) ==> Int.fdiv (a + b) 2` | `py_prove [midpoint]` | the honest `Int.fdiv` statement discipline; named statement enters inventory |
| 3 | Preconditions are hypotheses | `midpoint_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : midpoint(a, b) ==> (a + b) / 2` | `py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]` | preconditions-as-hypotheses, `py_corollary`, value bridging without re-execution |
| 4 | Fork in the road | `my_abs_spec : my_abs(x) ==> \|x\|` | `py_prove [my_abs]` | branching bodies; `py_prove`'s single-`split` recipe |
| 5 | **Boss: clamp01** | `clamp01_total : ag_clamp01.clamp01(x) ==> max 0 (min 1 x)` | `refine ⟨32, ?_⟩; by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;> py_simp [callFunction, ag_clamp01, h1, h2] <;> grind` | the documented boundary of `py_prove` (two sequential `if`s); `refine` (hand the fuel yourself — the move `py_check`/`py_prove` make internally), `py_simp`, `by_cases`, `grind`, `omega` (and why `omega` fails on `PyInt`-branded comparisons) |
| 6 | **Coda: the machine rises** | `clamp01_machine : ag_clamp01.clamp01(x) ==> min 1 (max 0 x)` | `py_vcgen [ag_clamp01]` + `all_goals omega` | `py_vcgen` (the VC walker: the whole L5 fight, generated), `all_goals`; the payoff framing — and the observation that the walker needs **no fuel**, which is why it survives loops |

(Verified during design: `py_prove [ag_clamp01]` genuinely fails on the boss —
the level teaches a real boundary, not a staged one. The coda states the
clamp with `min`/`max` nested the *other* way so its statement isn't literally
L5's.)

### World 3 — Loop World (built)

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
| 1 | Anatomy of a loop proof | `tri_total (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2` | full clause-mode proof as a visible `Template`; player fills two `grind` Holes (`case ret` finish + `all_goals`) | invariant/measure as clauses, the residual tags, `case`, `obtain`/`rfl`, `Int` |
| 2 | **Invent the invariant** (the heart) | same claim, anonymous | `py_vcgen [tri]` bare → player answers `inv1`/`dec1` with `exact fun total i => …`, then closes the residuals | delayed-goal mode; `exact`; the two honest failure modes (below) |
| 3 | The sum of odd numbers | `odd_sum_total (hn : 0 ≤ n) : odd_sum(n) ==> n * n` | clauses from scratch (`total = k * k` + range; `(n - k).toNat`), `all_goals grind` sweeps everything incl. `ret` | first from-scratch invariant; fresh envelope `odd_sum` (extracted with lean-surfaces' extractor) |
| 4 | The shadowed variable | `sum_to_total (N) (hN : 0 ≤ N) : sum_to(N) ==> N * (N + 1) / 2` | clauses with binders `(s n : Int)`; `case ret => obtain rfl : n' = 0` | the shadowing rule exactly as the gallery's reproved sum_to: the loop mutates Python's `n`, so the *theorem* binds the initial value as capital `N` and the clause binder `n` means the current value (the walker's counterpart of `py_loop`'s `(state := …)`) |
| 5 | Euclid's invariant | `gcd_total (hA : 0 ≤ A) (hB : 0 ≤ B) : gcd(A, B) ==> Int.gcd A B` | Template: clauses + 5 bullet residuals (exit-packaging bullet given; Holes for `Int.fmod_nonneg`, `gcd_fmod_step` rewrite, the `Int.fmod_lt_of_pos` measure argument, and the `grind [gcd_zero_right, natAbs_of_nonneg]` payout) | an invariant that is a *theorem* (gcd-preservation); the `Int.fmod` spec-side library as `NewTheorem`s; `rw`, `have` |
| 6 | **Boss: the nested machine** | `first_factor_even (hn : 2 ≤ n) (h2 : 2 ∣ n) : nested_flow.first_factor(n) ==> 2` | `have hn2` rebrand; `py_vcgen [nested_flow]` with **five clauses** (`inv1`/`dec1`, `inv2`/`dec2`, `exit2`); `all_goals grind` | numbered clauses for nested loops; the `exit` clause a `break` requires; outer invariant `i = 2` = an *unreachability* invariant (outer preserve/dec residuals are `⊢ False` with contradictory hyps) |

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
