import Game.Levels.LoopWorld.L02_InventInvariant

open LeanModels LeanModels.Python

World "LoopWorld"
Level 3

Title "Invent it again, doubled"

Introduction "
Fresh program, same skill:

```python
def double_sum(n):
    total = 0
    k = 0
    while k < n:
        total = total + 2 * k
        k = k + 1
    return total
```

`0 + 2 + 4 + ⋯` — the first `n` even numbers — and the claim is that they
sum to exactly `n * (n - 1)`.

Call the walker bare and answer its two requests, exactly as you just did
for `tri`. Invent, don't recall: after `k` laps, what is `total`? (This
time the books need no `2 *` trick — the sum *is* a product.) What keeps
`k` honest between entry and exit? What shrinks every lap?
"

/-- For every integer `n ≥ 0`, running `double_sum` terminates and returns
`n * (n - 1)`: the first `n` even numbers sum to a product. -/
Statement (n : PyInt) (hn : 0 ≤ n) : double_sum(n) ==> n * (n - 1) := by
  Hint "Open bare — `py_vcgen [double_sum]` — then answer `inv1` and `dec1`
  with `exact fun total k => …`. Books, range floor, range ceiling; then
  the distance remaining."
  py_vcgen [double_sum]
  Hint (hidden := true) "`case inv1 => exact fun total k => 0 ≤ k ∧ k ≤ n ∧ total = k * (k - 1)`"
  case inv1 => exact fun total k => 0 ≤ k ∧ k ≤ n ∧ total = k * (k - 1)
  Hint (hidden := true) "`case dec1 => exact fun total k => (n - k).toNat`"
  case dec1 => exact fun total k => (n - k).toNat
  Hint (hidden := true) "No division anywhere in the books, so no `ret`
  surgery is needed: the ceiling and the negated test pin `k' = n`, and
  `all_goals grind` sweeps everything."
  all_goals grind

Conclusion "
Second invariant invented, and this one closed without any `ret` surgery.
The guessing is becoming a reflex — good, because the programs stop being
polite from here.
"
