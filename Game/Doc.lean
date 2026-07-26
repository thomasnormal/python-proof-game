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

/-- `intro h` — when the goal is an implication `P → Q` (or a `∀`), move the
antecedent into the context as a hypothesis `h : P`, leaving `Q` to prove.

The move that opens every *negation* proof: `¬ P` in Lean **is** the
implication `P → False`, so on a goal `¬ P`, `intro h` hands you `h : P` and
the goal `False` — assume the impossible thing, then demolish it. -/
TacticDoc intro

/-- `by_cases h : P` splits the proof into two: one goal with `h : P`, one
with `h : ¬P`.

The house pattern for multi-`if` Python bodies: decide every test up front
(`by_cases h1 : x < 0 <;> by_cases h2 : 1 < x`), then hand the case facts to
`py_simp` so each of the four symbolic executions runs straight through. -/
TacticDoc by_cases

/-- `grind` is core Lean's general-purpose finisher: congruence closure plus
e-matching plus integer arithmetic over your hypotheses.

Why not `omega`? Two reasons that recur in this game. First, comparisons
*stated over the `PyInt` brand* — a statement binder's `0 < b`, a `by_cases`
split, a `b ≠ 0` goal of your own — elaborate brand-headed, and `omega`
skips anything whose head type is the brand; `grind` matches up to reducible
unfolding, so it sees through. Second, `omega` is strictly *linear*: a
product of two variables like `b * q` is out of its language, while `grind`
happily treats it as an atom and reasons around it. -/
TacticDoc grind

/-- `omega` decides linear integer arithmetic goals: anything built from
`Int`/`Nat` variables with `+`, `-`, `*`-by-constants, `≤`, `<`, `=`.

Caveats learned in this game: `omega` looks at the *head type* of each
comparison — a fact stated over the `PyInt` brand is invisible to it (use
`grind`, which unfolds reducible definitions). It atomizes anything else it
doesn't understand — `Int.fdiv a b` is an opaque symbol to it, and `b * q`
with both sides variables is out of its (linear) language. Inside its
language, though, it is a decision procedure: it *will* finish, e.g. by
refuting `-3 = -4`. -/
TacticDoc omega

/-- `py_vcgen [prog]` is the **VC-generating walker** — the whole manual
pipeline, mechanized. From a `f(args) ==> v` goal it bridges to the function
body and walks it statement by statement: straight-line segments are
discharged by captured symbolic execution, an `if` forks the walk per branch,
and each `while` is opened by the loop rule. Everything the interpreter can
answer is answered on the spot; what it cannot invent is *appended* as goals —
pure mathematics over named atoms, tagged by their role: `init` (the invariant
holds on entry), `preserve` (one loop body keeps it), `dec` (the measure
drops), `exit`/`ret` (from the exit facts to the returned value).

Loops need the two pieces of content no tactic can invent — the **invariant**
and the **decreasing measure**. Hand them over as clauses:

```
py_vcgen [prog]
  (inv := fun (x y : Int) => …)
  (dec := fun (x y : Int) => …)
```

The i-th `inv`/`dec` pair belongs to the i-th `while` (source order; label
them `inv1`, `dec1`, … when there are several). Binder names must be the
Python names of the variables **assigned in that loop's body**; everything
else stays pinned and can be mentioned directly. *Omit* the clauses and the
walker leaves them as delayed goals `inv1`/`dec1` — the proof pauses until you
invent the invariant. An `(exit := …)` clause states a loop's exit fact
explicitly — required when a `break` escapes a loop and the code after it
needs more than the bare invariant. -/
TacticDoc py_vcgen

/-- `all_goals tac` runs `tac` on every remaining goal and insists it closes
them all.

The house finisher after `py_vcgen`: the walker leaves a handful of
arithmetic residuals, and `all_goals grind` (or `all_goals omega`) sweeps
them in one line. Handle any goal that needs special treatment first (e.g.
with `case ret => …`), then sweep the rest. -/
TacticDoc all_goals

/-- `case tag => tac` focuses the (first) goal tagged `tag`.

`py_vcgen` tags everything it leaves behind: delayed loop clauses are
`inv1`, `dec1`, …; math residuals are `init`, `preserve`, `dec`, `exit`,
`ret`. So `case inv1 => …` answers the walker's request for an invariant,
and `case ret => …` picks out the return-value goal for special treatment
before an `all_goals` sweep. -/
TacticDoc case

/-- `exact e` closes the goal with the term `e`, exactly.

In this world you mostly use it to *hand over data*: a delayed clause goal
like `inv1 : Int → Int → Prop` is closed by
`exact fun total i => 0 ≤ i ∧ …` — not a proof, a *definition* of the
invariant. Assigning it instantiates every residual goal that mentions it. -/
TacticDoc exact

/-- `obtain pat : P := by tac` proves `P` on the side and destructs it into
the pattern `pat` — and the pattern `rfl` means: the proof is an equation,
*substitute it everywhere*.

The house move for exit algebra: after a loop, the negated test and the range
conjunct pin the loop variable (e.g. `i' = n + 1`); `obtain rfl : i' = n + 1
:= by omega` proves it and rewrites the goal, and the remaining algebra falls
to `grind`. -/
TacticDoc obtain

/-- `rfl` proves goals of the form `a = a` — both sides identical up to
computation.

In this game you'll mostly meet it as the *pattern* in
`obtain rfl : x = e := by …`: prove the equation, then substitute it
everywhere instead of keeping it as a hypothesis. -/
TacticDoc rfl

/-- `have h : P := e` (or `have h : P := by tac`) adds a proved fact `h : P`
to the context.

House uses, in order of appearance: **staging** — pull the pieces of an
argument into the context one line at a time (a run fact proved by
`py_prove`, the division-algorithm bounds, a determinism equation), then let
a finisher sweep the assembled facts; and **rebranding** — a hypothesis
stated over `PyInt` (the brand on statement binders) can be invisible to
`omega`, and `have hn2 : (2 : Int) ≤ n := hn` restates it at `Int` — same
proof, now `omega`-visible. -/
TacticDoc «have»

/-- `rw [h₁, h₂, …]` rewrites the goal left-to-right with the given
equations; `rw [← h]` rewrites right-to-left.

In Loop World it bridges *spec-side* algebra — e.g. rewriting with the
Euclid step `gcd_fmod_step` to show an invariant survives one loop
iteration. The interpreter is long gone by then; this is mathematics. -/
TacticDoc rw

/-- `f(args…) ==> v` — **total correctness**, the game's main judgment: the
Python call terminates and returns `v`. Formally `CallsTo m "f" #[…] v`:
*there exists* a fuel making the verified interpreter return `.ok v`. The
identifier is both the loaded module constant and the function name; a dotted
identifier `arith.mod(a, b)` splits into module `arith`, function `"mod"`.
Preconditions stay ordinary hypotheses. In hypothesis position the same
judgment can be written `f(args…) ⇓ r`, *binding* the result — see the `⇓`
entry. -/
DefinitionDoc LeanModels.Python.CallsTo as "==>"

/-- `f(args…) ==>! e` — **exceptions as specified behavior**: the call
terminates by *raising* `e` (a `PyErr`, e.g. `.zeroDivisionError`). Runtime
errors in the semantic tier are real and faithful — `7 % 0` doesn't “go
wrong”, it provably raises `ZeroDivisionError`, and that is a theorem you can
state and prove. -/
DefinitionDoc LeanModels.Python.Raises as "==>!"

/-- `f(args…) ⇓ r` — the **result-binding arrow**: exactly the same judgment
as `f(args…) ==> r`, written in *hypothesis position*. A hypothesis
`hq : arith.floordiv(a, b) ⇓ q` reads: “the call terminated, and `q` names
whatever it returned.” Because both arrows target the same judgment, the
goal view renders `⇓` as `==>` — the meaning is identical; only the role
differs: `==>` *states* what a run returns, `⇓` *binds* it so your theorem
can talk about the result without naming a formula for it.

Pair it with determinism (`CallsTo.typed_int_eq`) to replace the bound name
by a value you have proved. -/
DefinitionDoc ResultArrow as "⇓"

/-- `CallsTo.typed_int_eq : f(…) ⇓ r → f(…) ==> e → r = e` — **determinism**
of the verified interpreter, on the typed surface: one call cannot return
two different integers. Feed it two descriptions of the same run — typically
a `⇓` hypothesis binding an unknown result, and a spec theorem or `py_check`
fact you proved — and it welds them into an equation.

This is the engine behind `py_corollary`, used by hand: **run once, equate
forever**. It is also how you *refute* a wrong return value: two different
literals for one run collapse into a false equation like `-3 = -4`. -/
TheoremDoc LeanModels.Python.CallsTo.typed_int_eq as "CallsTo.typed_int_eq" in "Python programs"

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

/-- `Int.fmod a b` — **Python's `%`**: the remainder whose sign follows the
*divisor* (`7 % -2 == -1` in Python, and `Int.fmod 7 (-2) = -1`). It is the
partner of `Int.fdiv` in the division algorithm: quotient `Int.fdiv a b`,
remainder `Int.fmod a b`, and `Int.fmod_add_fdiv_mul` reassembles them into
`a`. Lean's own `%` on `Int` is Euclidean (`Int.emod`) — same honesty rule
as for `//`: theorems about Python's `%` say `Int.fmod`. -/
DefinitionDoc Int.fmod as "Int.fmod"

/-- `Int.fmod_add_fdiv_mul : a.fmod b + a.fdiv b * b = a` — **the division
algorithm**, in Python's dialect: floor-remainder plus floor-quotient times
divisor reassembles the dividend. This single equation, together with the
remainder's range (`Int.fmod_nonneg_of_pos`, `Int.fmod_lt_of_pos`),
*characterizes* what `//` and `%` compute — it is where “floor really
floors” comes from. -/
TheoremDoc Int.fmod_add_fdiv_mul as "fmod_add_fdiv_mul" in "Int"

/-- `Int.fmod_nonneg_of_pos : ∀ (a : Int), 0 < b → 0 ≤ a.fmod b` — for a
*positive divisor*, Python's `%` is never negative, whatever the sign of the
dividend (`-7 % 2 == 1` in Python). One half of the remainder's range; the
other half is `Int.fmod_lt_of_pos`. (Compare `Int.fmod_nonneg`, which asks
both operands to be nonnegative — here the dividend runs free.) -/
TheoremDoc Int.fmod_nonneg_of_pos as "fmod_nonneg_of_pos" in "Int"

/-- `rfl : a = a` — the proof that anything equals itself, computation
included.

You meet it in two costumes: as a *tactic* closing `a = a` goals, and as the
*pattern* in `obtain rfl : x = e := by …` — prove the equation, then
substitute it everywhere instead of carrying it around. -/
TheoremDoc rfl as "rfl" in "Logic"

/-- `Int` — Lean's arbitrary-precision integers, the type your *invariants*
speak.

Loop-clause binders are `Int`-valued: in
`(inv := fun (total i : Int) => …)` the binder names are the Python
variables the loop assigns, read back as honest integers. (`PyInt`, the
brand on statement binders, is definitionally `Int` — same numbers,
different hat.) -/
DefinitionDoc Int as "Int"

/-- `Int.gcd a b` — the greatest common divisor, as a spec-side function
(always nonnegative; `Int.gcd 0 b = |b|`). This is the *mathematical*
yardstick the Python `gcd` program is measured against — the program shuffles
`a, b = b, a % b`; the theorem says the answer is `Int.gcd a b`. -/
DefinitionDoc Int.gcd as "Int.gcd"

/-- The loaded program `odd_sum` — sums the first `n` odd numbers:

```python
def odd_sum(n):
    total = 0
    k = 0
    while k < n:
        total = total + 2 * k + 1
        k = k + 1
    return total
```

`1 + 3 + 5 + ⋯` — the classic. What it returns is prettier than what it
does. -/
DefinitionDoc odd_sum as "odd_sum" in "Python programs"

/-- The loaded program `sum_to` — triangular numbers again, but counting
**down**, mutating its own argument:

```python
def sum_to(n: int) -> int:
    s = 0
    while n > 0:
        s += n
        n -= 1
    return s
```

The Python variable `n` is *assigned in the loop body* — so in a loop clause,
the binder `n` must mean the current, mutated value. The name for the
initial value is up to your theorem statement (the house style: capital
`N`). -/
DefinitionDoc sum_to as "sum_to" in "Python programs"

/-- The loaded program `gcd` — Euclid's algorithm, verbatim:

```python
def gcd(a: int, b: int) -> int:
    while b != 0:
        a, b = b, a % b
    return a
```

Tuple assignment, and Python's `%` — which is `Int.fmod` (sign follows the
divisor), not Lean's `%`. The spec-side lemma `gcd_fmod_step` speaks exactly
that dialect. -/
DefinitionDoc gcd as "gcd" in "Python programs"

/-- The loaded module `nested_flow` — the final boss's lair:

```python
def first_factor(n: int) -> int:
    i = 2
    while i * i <= n:
        m = n
        while 0 < m:
            if m < i:
                break
            m = m - i
        if m == 0:
            return i
        i = i + 1
    return n
```

A `while` inside a `while`, a `break` inside an `if` in the inner body, and a
`return` out of the middle of the outer loop. Trial division where even the
divisibility *test* is a loop (repeated subtraction: `m == 0` afterwards
means `i` divides `n`). -/
DefinitionDoc nested_flow as "nested_flow" in "Python programs"

/-- `gcd_fmod_step : 0 ≤ a → 0 ≤ b → Int.gcd b (Int.fmod a b) = Int.gcd a b`
— Euclid's step in the exact shape the interpreter emits: Python's `%` is
`Int.fmod`, and swapping `(a, b) ↦ (b, a % b)` preserves the gcd. This is
the heart of the `gcd` loop invariant's preservation.

The sign hypotheses are not decoration: `Int.gcd 4 (-6) = 2`, but Python's
`4 % -6` is `-2` — and CPython agrees. -/
TheoremDoc LeanModels.Python.gcd_fmod_step as "gcd_fmod_step" in "Python programs"

/-- `Int.fmod_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a.fmod b` — Python's `%` never
goes negative when both operands are nonnegative. Keeps the `gcd` loop
invariant's range conjuncts alive across an iteration. -/
TheoremDoc Int.fmod_nonneg as "fmod_nonneg" in "Int"

/-- `Int.fmod_lt_of_pos : ∀ (a : Int), 0 < b → a.fmod b < b` — the remainder
is strictly smaller than a positive divisor. This is why Euclid *terminates*:
the measure `b.toNat` strictly drops each iteration. -/
TheoremDoc Int.fmod_lt_of_pos as "fmod_lt_of_pos" in "Int"

/-- `Int.gcd_zero_right : Int.gcd a 0 = a.natAbs` — when the loop is done
(`b = 0`), the gcd is just `|a|`. The last algebraic step of the `gcd`
proof. -/
TheoremDoc Int.gcd_zero_right as "gcd_zero_right" in "Int"

/-- `Int.natAbs_of_nonneg : 0 ≤ a → ↑a.natAbs = a` — drop the absolute value
when the sign is known. Pairs with `gcd_zero_right` to finish the `gcd`
return goal. -/
TheoremDoc Int.natAbs_of_nonneg as "natAbs_of_nonneg" in "Int"
