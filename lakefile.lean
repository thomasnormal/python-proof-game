import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

/-!
TOOLCHAIN RECONCILIATION NOTE (The Python Proof Game):
This game runs on `leanprover/lean4:v4.33.0-rc1` — the toolchain pinned by its
mathematical dependency, lean-surfaces (`lean-models`). lean4game's newest
release tag is `v4.31.0`, so `leanVersion` (= "v4.33.0-rc1") does NOT exist as
a lean4game tag; we hardcode the GameServer tag to `v4.31.0` below and pin
`batteries` at the root to its `v4.33.0-rc1` tag so the root pin shadows
GameServer's transitive `batteries @ v4.31.0` (root requires win over
transitive ones). `i18n` has no v4.33 tag either; we take `main` (v4.31.0)
and rely on it compiling under v4.33.0-rc1.
-/
def gameServerVersion : String := "v4.31.0"

/--
Use the GameServer from a `lean4game` folder lying next to the game on your local computer.
Activated with `lake update -Klean4game.local`.
-/
def LocalGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := some (DependencySrc.path "../lean4game/server")
  version := .none
  opts := ∅
}

/--
Use the GameServer version from github.
Deactivate local version with `lake update -R`.
-/
def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := some (DependencySrc.git "https://github.com/leanprover-community/lean4game.git"
    (some gameServerVersion) (some "server"))
  version := .git gameServerVersion
  opts := ∅
}

/-
Choose GameServer dependency depending on whether `-Klean4game.local` has been passed to `lake`.
-/
open Lean in
#eval (do
  let gameServerName := if get_config? lean4game.local |>.isSome then
    ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
  : Elab.Command.CommandElabM Unit)

/-!
# USER DEPENDENCIES

Add any further dependencies of your game below.

Note: If your package (like `mathlib` or `Std`) has tags of the form `v4.X.0` then
you can use

```
require "leanprover-community" / mathlib @ git leanVersion
```
 -/

-- require "leanprover-community" / mathlib @ git leanVersion

/- Root-level pin: shadows GameServer's transitive `batteries @ v4.31.0`,
which would not compile under the v4.33.0-rc1 toolchain. -/
require "leanprover-community" / batteries @ git leanVersion

/- lean-surfaces: the framework this game teaches. Pinned to the exact rev the
levels were written against (its own toolchain is v4.33.0-rc1, matching ours).
For local iteration you may instead use a path dependency:
  require «lean-models» from "/home/thomas-ahle/lean_models"
but the git form below is the publication-ready one. -/
require «lean-models» from git
  "https://github.com/thomasnormal/lean-surfaces" @ "0ff4bb705b560387c5b9635b8bcdde5289544671"

/-!
# PACKAGE CONFIGURATION

Here you can set options used in your game. The player will use the same options as you'll
have set here.

NOTE: The `leanOptions` and `moreServerOptions` influence how the player preceives the game.
For example, it is important to have `linter.all` set to `false` to prevent any linter
warnings from showing up during playing.

NOTE: We abuse the `trace.debug` option to toggle messages in VSCode on and
off when calling `lake build`. Ideally there would be a better way using `logInfo` and
an option like `lean4game.verbose`.
-/
package Game where
  /- Used in all cases. -/
  leanOptions := #[
    /- linter warnings might block the player. (IMPORTANT) -/
    ⟨`linter.all, false⟩,
    /- to display the values of let declarations, like `:= 42` (IMPORTANT)  -/
    ⟨`pp.showLetValues, true⟩,
    /- make all assumptions always accessible. -/
    ⟨`tactic.hygienic, false⟩]
  /- Used when calling `lake build`. -/
  moreLeanArgs := #[
    -- TODO: replace with `lean4game.verbose`
    "-Dtrace.debug=false"]
  /- Used when opening a file in VSCode or when playing the game. -/
  moreServerOptions := #[
    -- TODO: replace with `lean4game.verbose`
    ⟨`trace.debug, true⟩]

@[default_target]
lean_lib Game
