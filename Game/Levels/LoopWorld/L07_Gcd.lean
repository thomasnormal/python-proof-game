import Game.Levels.LoopWorld.L06_Steps

open LeanModels LeanModels.Python

World "LoopWorld"
Level 7

Title "Euclid's invariant"

Introduction "
The oldest named algorithm, verbatim:

```python
def gcd(a: int, b: int) -> int:
    while b != 0:
        a, b = b, a % b
    return a
```

The claim: for `A, B ≥ 0`, this returns `Int.gcd A B`. Both variables are
assigned (tuple assignment), so both are clause binders, with capital
theorem binders for the initial values: the `sum_to` move, twice.

Every invariant so far was bookkeeping. This one is a **theorem of
Euclid's**: the pair changes every lap, but its gcd never does —

`inv := fun (a b : Int) => 0 ≤ a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B`

with measure `b.toNat` — the remainder shrinks. This time the residuals are
*number theory*; a bare `grind` won't carry them — you close them `case`
by `case` with the `Int.fmod` library in your inventory
(Python's `%` *is* `Int.fmod`). `exit` is written out in the editor;
`preserve`, `preserve2`, `dec`, `ret` are yours.

The sign hypotheses on those lemmas are not decoration —
`Int.gcd 4 (-6) = 2` but Python computes `4 % -6 == -2` (CPython agrees).
Your `0 ≤ a ∧ 0 ≤ b` conjuncts are what feed them.
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
    Hint "Five tagged goals. The `exit` one is written out for you in the
    editor — read its `⟨…⟩` term: witness the final `a`, hand over the exit
    facts (`rfl`, `hx`), the range fact `hcore.1`, and a `by rw [...]` for
    the last algebra. The other four are yours, each by name:
    `case preserve`, `case preserve2` (same-tag goals get numbered),
    `case dec`, `case ret`."
    case exit =>
      exact ⟨a, ⟨rfl, hx⟩, hcore.1, by rw [← hcore.2.2, hx, Int.gcd_zero_right]⟩
    case preserve =>
      Hint (hidden := true) "The `Int.fmod` kit, by name: this goal *is*
      `Int.fmod_nonneg hinv1 hinv2` — `exact` it. Next door, `case preserve2`
      wants `rw [gcd_fmod_step hinv1 hinv2]` and then the old invariant
      `hinv3`; and `case dec` wants `Int.fmod_lt_of_pos` and
      `Int.fmod_nonneg` staged with `have`, then `omega`."
      Hole exact Int.fmod_nonneg hinv1 hinv2
    case preserve2 =>
      Hole rw [gcd_fmod_step hinv1 hinv2]
           exact hinv3
    case dec =>
      Hole have h1 := Int.fmod_lt_of_pos a (b := b) (by omega)
           have h2 := Int.fmod_nonneg hinv1 hinv2
           omega
    case ret =>
      Hint (hidden := true) "A bare `grind` stalls here — it needs the two
      payout theorems as ammunition, in brackets:
      `grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]`."
      Hole grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]

Conclusion "
Twenty-three centuries later, Euclid's argument types out in five tagged
goals.

Notice what the proof did *not* contain: a single unfolding of the
interpreter. The walker ate the semantics; you supplied mathematics —
`gcd_fmod_step` is literally Proposition VII.2, restated over the `%` of a
programming language that ships on a billion machines.

That was the hardest hand-work in the world. Next level is a breather — and
a payday.
"

NewTactic rw
NewTheorem LeanModels.Python.gcd_fmod_step Int.fmod_nonneg
  Int.gcd_zero_right Int.natAbs_of_nonneg
NewDefinition gcd Int.gcd
