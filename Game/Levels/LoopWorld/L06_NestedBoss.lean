import Game.Levels.LoopWorld.L05_Gcd

open LeanModels LeanModels.Python

World "LoopWorld"
Level 6

Title "Boss: the nested machine"

Introduction "
The final boss guards three shapes at once:

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

A `while` **inside** a `while`; a **`break`** inside an `if` in the inner
body; a **`return` out of the middle of the outer loop**. Trial division
where even the divisibility test is a loop — repeated subtraction, so
`m == 0` afterwards means `i` divides `n`.

Your claim: **if `n ≥ 2` is even, `first_factor(n)` returns `2`.** (The
unconditional theorem — smallest *prime* factor for every `n ≥ 2` — is
proved with this exact clause structure in the lean-surfaces gallery; its
residuals need mathlib's `minFac` machinery, so the game keeps the even
case, where every leftover is elementary. The *shape* you fight is the full
monster.)

What the shape demands:

* **Two loops → numbered clauses.** `inv1`/`dec1` for the outer loop (source
  order), `inv2`/`dec2` for the inner.
* **The outer invariant is a trick question.** When `2 ∣ n`, the inner loop
  drives `m` all the way to `0`, so the function returns *during the first
  outer lap* — `i` never reaches `3`. The honest invariant is just `i = 2`,
  and outer preservation will ask you for `False` with contradictory
  hypotheses in hand: proving the lap *unreachable* is proving the loop
  never laps. (Measure: `(n - i).toNat` — anything sane works for a loop
  that never laps.)
* **The inner invariant** is subtraction bookkeeping: `m` stays nonnegative
  and `2 ∣ (n - m)` — the loop only ever removes `i = 2` at a time. Measure:
  `m.toNat`.
* **The `break` needs an `exit2` clause.** A loop with a `break` has *two*
  doors out, and the bare invariant plus negated test only describes one.
  `(exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m))` states
  what is true at *either* door — the walker then makes the test-false door
  imply it and makes the `break` site (branch fact `m < i` in hand) establish
  it. Note it may mention the outer `i` by name. And you don't have to know
  any of this in advance: call `py_vcgen [nested_flow]` *bare* and the
  walker asks for everything it needs — `inv1`, `dec1`, `inv2`, `dec2`,
  **and** an `exit2` clause goal for the `break`-carrying loop. The exit
  clause is a first-class request, not folklore.

Assemble the call, then sweep — every residual the walker leaves is
elementary, and `all_goals grind` clears the board. (No housekeeping
needed: `grind` reads the branded precondition `hn` as it stands.)
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
  Hint "The full call — five clauses: outer `inv1 := fun (i : Int) => i = 2`
  and `dec1 := fun (i : Int) => (n - i).toNat`; inner
  `inv2 := fun (m : Int) => 0 ≤ m ∧ (2:Int) ∣ (n - m)` and
  `dec2 := fun (m : Int) => m.toNat`; and the break's
  `exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m)`.

  All in one `py_vcgen [nested_flow] (…) (…) (…) (…) (…)` call."
  py_vcgen [nested_flow]
    (inv1 := fun (i : Int) => i = 2)
    (dec1 := fun (i : Int) => (n - i).toNat)
    (inv2 := fun (m : Int) => 0 ≤ m ∧ (2:Int) ∣ (n - m))
    (dec2 := fun (m : Int) => m.toNat)
    (exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ (2:Int) ∣ (n - m))
  Hint "Nine residuals — the outer `exit`, the inner `init`, the two doors
  of the inner exit (`exit2` and `exit3` — same-tag goals get numbered),
  inner preservation and decrease (`preserve`, `dec`), outer preservation
  and decrease (`preserve2`, `dec2` — both with *contradictory* hypotheses:
  the lap is unreachable, `False` is provable), and the final `return n`
  (`ret`) — every one elementary. Sweep: `all_goals grind`."
  all_goals grind

Conclusion "
**Loop World cleared.**

Stand back and look at what you just proved: a nested loop, a `break`, a
`return` from the middle of a loop — *three* control shapes the framework's
older single-loop tactic could not open at all, walked by `py_vcgen` from
five clauses you wrote. The outer invariant was a statement about
*unreachability*; the `exit2` clause was you, stating what is true at the
moment of escape — through either door.

And the residuals stayed elementary because the *specification* was chosen
honestly: the even case. The unconditional smallest-prime-factor theorem is
this same clause skeleton with number theory in the residuals — it lives in
the lean-surfaces gallery (`Examples/python/nested_flow`), and after this
fight you can read it like a menu.

Beyond this door: **RSA World** — `extended_gcd` and `inverse` from the
shipped `python-rsa` library, byte-verbatim, where the docstring's invariant
is subtly wrong and the honest one is seven variables wide. The machinery in
your hands is exactly the machinery that proof uses.
"

NewDefinition nested_flow
