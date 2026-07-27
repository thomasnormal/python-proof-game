import Game.Levels.LoopWorld.L08_GcdComm

open LeanModels LeanModels.Python

World "LoopWorld"
Level 9

Title "Boss: the nested machine"

Introduction "
The final boss — the **toughest fight in the game**. Three shapes at once:

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

A `while` **inside** a `while`; a **`break`** inside an `if`; a
**`return`** from mid-loop. Trial division where even the divisibility test
is a loop — `m == 0` after repeated subtraction means `i` divides `n`.

Your claim: **if `n ≥ 2` is even, `first_factor(n)` returns `2`.** (The
unconditional smallest-prime-factor theorem is this same skeleton with
number theory in the residuals — see the lean-surfaces gallery. Here you
fight the full *shape*.)

Two loops mean **numbered clauses**: `inv1`/`dec1` outer, `inv2`/`dec2`
inner, source order. And the `break` gives the inner loop *two* doors out,
so it needs an **`exit2` clause** — a fact true at *either* door. No need
to memorize this: call `py_vcgen [nested_flow]` **bare** and the walker
requests everything it needs, `exit2` included.

A trick question waits in the outer loop: when `n` is even, how many laps
actually run?
"

/-- `first_factor(n) ==> 2` for even `n ≥ 2` — total correctness through a
nested loop, a `break`, and a mid-loop `return`, from five clauses: two
invariant/measure pairs and an explicit `exit2` fact for the `break`. -/
TheoremDoc first_factor_even as "first_factor_even" in "Python programs"

/-- For every even integer `n ≥ 2`, running `first_factor` terminates and
returns `2` — through a nested loop, a `break`, and a `return` from the
middle of the outer loop. -/
Statement first_factor_even (n : PyInt) (hn : 2 ≤ n) (h2 : (2:Int) ∣ n) :
    nested_flow.first_factor(n) ==> 2 := by
  Hint "Five clauses in one `py_vcgen [nested_flow] (…) (…) (…) (…) (…)`
  call — or bare, answering the requests one at a time. The trick question:
  when `2 ∣ n`, the inner loop drives `m` to `0` and the function returns
  *during the first outer lap* — `i` never reaches `3`. An invariant for a
  loop that never laps can simply pin the counter; outer preservation then
  hands you contradictory hypotheses, and proving `False` is proving the
  lap unreachable. The inner loop is subtraction bookkeeping: it only ever
  removes `2` at a time."
  Hint (hidden := true) "The full call: outer
  `inv1 := fun (i : Int) => i = 2`,
  `dec1 := fun (i : Int) => (n - i).toNat` (anything sane works for a loop
  that never laps); inner
  `inv2 := fun (m : Int) => 0 ≤ m ∧ (2:Int) ∣ (n - m)`,
  `dec2 := fun (m : Int) => m.toNat`; and the break's
  `exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m)` — note it
  may mention the outer `i` by name."
  py_vcgen [nested_flow]
    (inv1 := fun (i : Int) => i = 2)
    (dec1 := fun (i : Int) => (n - i).toNat)
    (inv2 := fun (m : Int) => 0 ≤ m ∧ (2:Int) ∣ (n - m))
    (dec2 := fun (m : Int) => m.toNat)
    (exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m))
  Hint "Nine residuals — the two doors of the inner exit, inner and outer
  preservation and decrease (the outer pair with *contradictory*
  hypotheses: the lap is unreachable, `False` is provable), `init`, `exit`,
  and the final `return n` — every one elementary. Sweep them."
  Hint (hidden := true) "`all_goals grind` clears the board — it reads the
  branded precondition `hn` as it stands."
  all_goals grind

Conclusion "
**Loop World cleared.**

Stand back: a nested loop, a `break`, a `return` from the middle of a loop
— walked by `py_vcgen` from five clauses you wrote, with an
*unreachability* invariant and an escape-door fact of your own. The
unconditional smallest-prime-factor theorem is this same clause skeleton
with number theory in the residuals; it lives in the lean-surfaces gallery
(`Examples/python/nested_flow`), and after this fight you can read it like
a menu.

Beyond this door: **RSA World** — `extended_gcd` and `inverse` from the
shipped `python-rsa` library, byte-verbatim, where the docstring's
invariant is subtly wrong and the honest one is seven variables wide. The
machinery in your hands is exactly the machinery that proof uses.
"
