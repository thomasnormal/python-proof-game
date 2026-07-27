import Game.Levels.StraightLineWorld.L05_MidpointDiv

open LeanModels LeanModels.Python

World "StraightLineWorld"
Level 6

Title "Fork in the road"

Introduction "
Control flow enters the chat:

```python
def my_abs(x: int) -> int:
    if x < 0:
        return -x
    return x
```

With `x` symbolic, the interpreter cannot know which branch runs — the test
`x < 0` has no answer yet. Symbolic execution leaves the choice behind as a
mathematical `if … then … else`, and the goal compares *that* to `|x|`.

Good news: `py_prove` has a branching mode. When a lone `if` survives
execution, it splits the two cases and finishes each side with `omega`
(which knows `|·|` on integers natively).

Same one call as always — but watch the Conclusion for the fine print on the
word *lone*.
"

/-- `my_abs(x) ==> |x|` for every integer — the first branching body:
`py_prove` splits the surviving `if` and closes both sides with `omega`. -/
TheoremDoc my_abs_spec as "my_abs_spec" in "Python programs"

/-- For every integer `x`, running `my_abs` terminates and returns the
absolute value `|x|`. -/
Statement my_abs_spec (x : PyInt) : my_abs(x) ==> |x| := by
  Hint "Branching bodies are still `py_prove` territory: `py_prove [my_abs]`.
  It executes symbolically, `split`s the surviving `if`, and closes both
  branches with `omega`."
  py_prove [my_abs]

Conclusion "
Two branches, one call. `py_prove`'s recipe: execute, `split` the surviving
`if`, `omega` both sides.

The fine print: that recipe performs **one** split. A body with *two
sequential* `if`s leaves a shape it cannot attack. Guess what the next level
is.
"

NewDefinition my_abs
