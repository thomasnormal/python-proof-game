# The Python Proof Game — plan

A [lean4game](https://github.com/leanprover-community/lean4game) that teaches
formal verification of **real Python programs** using the
[lean-surfaces](https://github.com/thomasnormal/lean-surfaces) framework
(deep-embedded Python in Lean 4, verified interpreter differentially tested
against CPython, typed spec surface: `f(a) ==> v`, `py_prove`, `py_loop`, …).

## Status

- **Built and green**: Worlds 1–2 (9 levels), full `lake build` including
  `MakeGame`; gamedata generated at `.lake/gamedata/`.
- **Designed, not built**: Worlds 3–4 (below).
- Local-only repository; not yet published anywhere.

## Toolchain findings (the critical reconciliation)

| Component | Version | Note |
|---|---|---|
| Game toolchain | `leanprover/lean4:v4.33.0-rc1` | matches lean-surfaces exactly |
| lean-surfaces (`lean-models`) | git `60ae7c8df622d50fc3a5a10cba082d3e64d5bd0c` | == public `master` == local `/home/thomas-ahle/lean_models` master; first rev with the `py_check` tactic |
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

(Verified during design: `py_prove [ag_clamp01]` genuinely fails on the boss —
the level teaches a real boundary, not a staged one.)

### World 3 — Loop World (designed, not built)

`while` loops: the two pieces of content no tactic can invent — the
**invariant** and the **decreasing measure** — via `py_begin [prog]` +
`py_loop (inv := …) (dec := …)` (LoopTactic.lean). Envelope `sum_to.json` is
already bundled and loaded in `Game/Programs.lean`.

Planned levels, with the Template/Hole invariant pedagogy — lean4game's
`Template`/`Hole` tactics let a level ship the proof *skeleton* with only the
invariant (or only the measure) as a hole, so each level isolates exactly one
new cognitive load:

1. **Loop, concretely** — `tri(6) ==> 21` by `py_check`:
   loops cost nothing when inputs are concrete; sets up the contrast.
2. **Read an invariant** — `tri_total (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2`,
   full proof given as visible Template (as W1L4 did for `py_prove`):
   `py_begin [tri]` + `py_loop (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)) (dec := fun (total i : Int) => (n + 1 - i).toNat)`
   + exit algebra `obtain rfl : i' = n + 1 := by omega; grind` + `all_goals grind`.
   The level's text walks through what each residual goal *is* (exit algebra,
   preservation, measure decrease, initial invariant).
3. **Fill in the measure** — same theorem, Template with `dec := Hole` (the
   invariant given); player supplies `(n + 1 - i).toNat`.
4. **Fill in the invariant** — `sum_to_total (hn : 0 ≤ n) : sum_to(n) ==> n * (n + 1) / 2`,
   Template gives the scaffold incl. `(state := [s, n])` (the countdown loop
   mutates `n`, the binder-shadowing escape hatch) and `dec := fun (s k : Int) => k.toNat`;
   player supplies `inv := fun (s k : Int) => 0 ≤ k ∧ k ≤ n ∧ 2 * s = (n - k) * (n + k + 1)`.
   Hints keyed to each residual goal.
5. **Boss: gcd** — `Examples/python/gcd` (envelope to be bundled): Euclid's
   loop, invariant over `%`, the `gcd_emod_step`/`gcd_fmod_step` spec-side
   lemmas from Surface.lean as `NewTheorem`s.

New inventory: `py_begin`, `py_loop`, `obtain`, `all_goals` (+ TacticDocs
adapted from LoopTactic.lean's excellent docstrings). Risk to test when
building: `py_loop`'s named-argument atoms (`inv`, `dec`, `state`) vs the
game's atom-based tactic checker — if the checker flags `inv`/`dec` as
"tactics", they may need adding to a hidden inventory entry or upstream
`ALLOWED_KEYWORDS`. (`only`, `at`, `fun`, `if/then/else` are already
whitelisted; `inv`/`dec`/`state` are not.)

### World 4 — RSA World (designed, not built)

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

## Publication checklist (per lean4game docs)

Everything below is deliberately **not done** (local-only mandate):

- [ ] Create a public GitHub repository (e.g. `thomasnormal/python-proof-game`)
      and push.
- [x] Game metadata in `Game.lean`: `Title`, `Introduction`, `Info`,
      `Languages "en"`, `CaptionShort`, `CaptionLong` (all set;
      `Prerequisites`/`CoverImage` optional — a cover image at ≤ ~500×200 px
      under `images/` is the one nice-to-have still missing).
- [x] Dependency form: the lakefile already uses the **git** dependency on
      `https://github.com/thomasnormal/lean-surfaces` pinned to rev
      `60ae7c8d…` (no path deps anywhere), so the repo is publication-ready
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
