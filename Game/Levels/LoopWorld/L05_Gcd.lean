import Game.Levels.LoopWorld.L04_SumTo

open LeanModels LeanModels.Python

World "LoopWorld"
Level 5

Title "Euclid's invariant"

Introduction "
The oldest algorithm with a name, verbatim:

```python
def gcd(a: int, b: int) -> int:
    while b != 0:
        a, b = b, a % b
    return a
```

The claim: for `A, B ≥ 0`, this returns `Int.gcd A B`. Both variables are
assigned (tuple assignment), so both are clause binders — and both initial
values get capitalized theorem binders `A`, `B`, exactly the sum_to move,
twice.

So far every invariant was bookkeeping. This one is a **theorem of
Euclid's**: the pair `(a, b)` changes every lap, but its gcd never does —

`inv := fun (a b : Int) => 0 ≤ a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B`

with measure `b.toNat` (the remainder strictly shrinks). The residuals this
time are *number theory*, and `grind` alone won't carry them — you'll close
them one by one with the spec-side library (part fresh in your inventory,
part carried since “Floor means floor”, all stated over `Int.fmod`, because
Python's `%` *is* `Int.fmod`). In walk order, with `·` focusing each goal:

1. **exit** — package the answer at `b = 0`: witness the final `a`, then
   `Int.gcd a 0 = a.natAbs` closes it. Given below — read it, it's the
   shape from L1's `exit`, by hand.
2. **preserve, part 1** — the new remainder is nonnegative:
   `Int.fmod_nonneg`.
3. **preserve, part 2** — the gcd survives the swap: rewrite with
   `gcd_fmod_step` (that *is* Euclid's lemma), then the old invariant.
4. **dec** — the remainder shrinks: `Int.fmod_lt_of_pos`, plus
   `Int.fmod_nonneg` to clear the `max`, then `omega`.
5. **ret** — cash out: `grind` with `Int.gcd_zero_right` and
   `Int.natAbs_of_nonneg`.

The sign hypotheses on those lemmas are not decoration — `Int.gcd 4 (-6) = 2`
but Python computes `4 % -6 == -2` (CPython agrees; it's in the differential
test suite). Your `0 ≤ a ∧ 0 ≤ b` conjuncts are what feed them.
"

/-- `gcd(A, B) ==> Int.gcd A B` for all `A, B ≥ 0` — Euclid's algorithm
returns the greatest common divisor, via the invariant that is Euclid's
lemma itself: `Int.gcd a b` never changes. -/
TheoremDoc gcd_total as "gcd_total" in "Python programs"

/-- For all integers `A, B ≥ 0`, running `gcd` terminates and returns
`Int.gcd A B`. The invariant: the running pair always has the *original*
gcd. -/
Statement gcd_total (A B : PyInt) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    gcd(A, B) ==> Int.gcd A B := by
  Template
    py_vcgen [gcd]
      (inv := fun (a b : Int) => 0 ≤ a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B)
      (dec := fun (a b : Int) => b.toNat)
    · exact ⟨a, ⟨rfl, hx⟩, hcore.1, by rw [← hcore.2.2, hx, Int.gcd_zero_right]⟩
    · Hole exact Int.fmod_nonneg hinv1 hinv2
    · Hole rw [gcd_fmod_step hinv1 hinv2]
           exact hinv3
    · Hole have h1 := Int.fmod_lt_of_pos a (b := b) (by omega)
           have h2 := Int.fmod_nonneg hinv1 hinv2
           omega
    · Hole grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]

Conclusion "
Twenty-three centuries later, Euclid's argument types out in five bullets.

Notice what the proof did *not* contain: a single unfolding of the
interpreter. The walker ate the semantics; you supplied mathematics —
`gcd_fmod_step` is literally Proposition VII.2, restated over the `%` of a
programming language that ships on a billion machines.

One level left. Bring everything.
"

NewTactic rw
NewTheorem LeanModels.Python.gcd_fmod_step Int.fmod_nonneg
  Int.gcd_zero_right Int.natAbs_of_nonneg
NewDefinition gcd Int.gcd
