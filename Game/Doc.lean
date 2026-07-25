import Game.Metadata
import Game.Programs

/-!
# Inventory documentation

TacticDoc / DefinitionDoc / TheoremDoc entries for everything the game
introduces. The one-paragraph tactic docs are adapted from the lean-surfaces
docstrings (`LeanModels/Python/Surface.lean`, `LoopTactic.lean`).

Exception: `TheoremDoc` for a *named `Statement`* must live in the same file
as the `Statement` (GameServer quirk), so `midpoint_spec`'s doc lives in its
level file, not here.
-/

/-- `py_check` closes a concrete-run goal — `f(args) ==> v` or
`f(args) ==>! e` with every argument a literal — by making Lean **actually
run the program** inside the proof.

Under the hood it donates a generous fuel budget (4096 steps — extra fuel is
harmless, a finished run keeps its result) and asks the kernel to compute the
run down to `.ok v` (resp. `.exn e`). No test framework, no mocking: the
Python program executes inside the proof checker.

It refuses symbolic goals on principle — a free variable means there is
nothing concrete to run. That is `py_prove`'s territory. -/
TacticDoc py_check

/-- `refine e` fills in the goal with the expression `e`, leaving every `?_`
inside `e` as a new goal.

In this game its job is handing the interpreter its fuel *by hand*:
`refine ⟨32, ?_⟩` turns the claim “*some* amount of fuel makes this Python
call finish” into the concrete claim “fuel `32` does” — exactly what
`py_check` and `py_prove` do for you internally. At the boss you take the
wheel yourself. Extra fuel is always harmless — a finished run keeps its
result. -/
TacticDoc refine

/-- `py_prove [prog]` closes total-correctness goals (`f(a, b) ==> v`,
`f(a) ==>! e`) for straight-line *and single-branching* loop-free bodies.

It commits a fuel witness, symbolically executes the interpreter with
`py_simp` (pass the loaded program constant, e.g. `py_prove [add]`), and
discharges the residual value equations with `rfl`/`omega`. If a symbolic
`if` survives as an `ite`, it `split`s the branches and finishes each side
with `omega`.

Its limit is honest: *two sequential* `if`s produce a shape its single-`split`
recipe cannot attack — that is the boss level of Straight-Line World. -/
TacticDoc py_prove

/-- `py_corollary [tot, extras…]` closes a standard corollary of an already
proved total-correctness theorem `tot` — *without re-executing the program*.

It handles the gallery corollary shapes, in particular a value-rewritten
`==>` restatement: `⊢ f(n) ==> v'` where `v'` is propositionally (not
definitionally) equal to `tot`'s value. Side hypotheses of `tot` (like
`0 ≤ n`) are discharged by `assumption`; when plain unification cannot bridge
the two value forms, it normalizes with the `extras` as rewrite rules — e.g.
`py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]`. -/
TacticDoc py_corollary

/-- `py_simp [facts…]` is the framework's symbolic-execution workhorse: `simp`
armed with the interpreter's equations. Passing the loaded program constant
(e.g. `ag_clamp01`) unfolds the Python AST; passing `callFunction` starts the
call; passing hypotheses (e.g. a `by_cases` fact `h1 : x < 0`) resolves the
branch tests the symbolic input leaves open.

`py_prove` uses it internally — you reach for `py_simp` yourself when a body's
shape falls outside `py_prove`'s recipe. -/
TacticDoc py_simp

/-- `by_cases h : P` splits the proof into two: one goal with `h : P`, one
with `h : ¬P`.

The house pattern for multi-`if` Python bodies: decide every test up front
(`by_cases h1 : x < 0 <;> by_cases h2 : 1 < x`), then hand the case facts to
`py_simp` so each of the four symbolic executions runs straight through. -/
TacticDoc by_cases

/-- `grind` is core Lean's general-purpose finisher: congruence closure plus
e-matching over your hypotheses.

Why not `omega` here? With binders at `PyInt` (a brand for `Int`), comparisons
introduced by `by_cases` elaborate brand-headed, and `omega` skips any
comparison whose head type is the brand. `grind` matches up to reducible
unfolding, so it sees through the brand and closes the arithmetic. -/
TacticDoc grind

/-- `omega` decides linear integer arithmetic goals: anything built from
`Int`/`Nat` variables with `+`, `-`, `*`-by-constants, `≤`, `<`, `=`.

Caveat learned in this game: `omega` looks at the *head type* of each
comparison. A hypothesis stated over the `PyInt` brand can be invisible to it
— when that happens, use `grind`, which unfolds reducible definitions. -/
TacticDoc omega

/-- `f(args…) ==> v` — **total correctness**, the game's main judgment: the
Python call terminates and returns `v`. Formally `CallsTo m "f" #[…] v`:
*there exists* a fuel making the verified interpreter return `.ok v`. The
identifier is both the loaded module constant and the function name; a dotted
identifier `arith.mod(a, b)` splits into module `arith`, function `"mod"`.
Preconditions stay ordinary hypotheses. -/
DefinitionDoc LeanModels.Python.CallsTo as "==>"

/-- `f(args…) ==>! e` — **exceptions as specified behavior**: the call
terminates by *raising* `e` (a `PyErr`, e.g. `.zeroDivisionError`). Runtime
errors in the semantic tier are real and faithful — `7 % 0` doesn't “go
wrong”, it provably raises `ZeroDivisionError`, and that is a theorem you can
state and prove. -/
DefinitionDoc LeanModels.Python.Raises as "==>!"

/-- The loaded program `tri` — the game's opening act:

```python
def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total
```

A literal `Module` AST term, ingested from the extractor's JSON envelope at
build time. Pass a program constant to `py_prove`/`py_simp` in brackets so
the tactic can unfold the code. -/
DefinitionDoc tri as "tri" in "Python programs"

/-- The loaded program `add` — two arguments, one `+`:

```python
def add(a, b):
    return a + b
```
-/
DefinitionDoc add as "add" in "Python programs"

/-- The loaded program `midpoint`:

```python
def midpoint(a: int, b: int) -> int:
    return (a + b) // 2
```

Remember: `//` floors. -/
DefinitionDoc midpoint as "midpoint" in "Python programs"

/-- The loaded program `my_abs` — one `if`, two branches:

```python
def my_abs(x: int) -> int:
    if x < 0:
        return -x
    return x
```
-/
DefinitionDoc my_abs as "my_abs" in "Python programs"

/-- The loaded module `arith` — a grab bag of one-liners; the game uses:

```python
def floordiv(a, b):
    return a // b

def mod(a, b):
    return a % b
```

Call functions of a module with dotted names: `arith.mod(7, 0)`. -/
DefinitionDoc arith as "arith" in "Python programs"

/-- The loaded program `ag_clamp01` — the boss of Straight-Line World:

```python
def clamp01(x):
    if x < 0:
        return 0
    if x > 1:
        return 1
    return x
```

Two *sequential* `if`s — the documented boundary of `py_prove`'s recipe. -/
DefinitionDoc ag_clamp01 as "ag_clamp01" in "Python programs"

/-- `callFunction m f args fuel` — **the verified interpreter**: an
executable Lean definition that runs function `f` of module `m` on `args`
with a step budget of `fuel`. Every judgment in this game unfolds to a
statement about it, and it is differentially tested against CPython. Pass it
to `py_simp` to start a call's symbolic execution. -/
DefinitionDoc LeanModels.Python.callFunction as "callFunction"

/-- `Int.fdiv a b` — **floor division**, rounding toward −∞. This is what
Python's `//` *actually does*: `(-1) // 2 = -1` in Python, not `0`.

Lean's `Int` division zoo, for the record: `Int.div` truncates toward zero,
`/` on `Int` (this toolchain) is Euclidean division `Int.ediv`, and
`Int.fdiv` floors. Honest theorems about Python `//` must say `Int.fdiv` —
the divergence belongs in the statement, never buried in a translation. -/
DefinitionDoc Int.fdiv as "Int.fdiv"

/-- `Int.fdiv_eq_ediv_of_nonneg : ∀ (a : Int) {b : Int}, 0 ≤ b →
a.fdiv b = a / b` — the bridge between Python's floor division and Lean's `/`
(Euclidean division): they agree whenever the *divisor* is nonnegative (here,
`2`). Feed it to `py_corollary` as a value rewrite to restate an `Int.fdiv`
result in `/` form. -/
TheoremDoc Int.fdiv_eq_ediv_of_nonneg as "fdiv_eq_ediv_of_nonneg" in "Int"
