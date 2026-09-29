# Cantor's diagonal argument in Lean 4

List infinite binary sequences, one per row. Flip every bit on the diagonal. The new sequence differs
from row `n` at position `n`, so it is on no row: no list contains every binary sequence.

```
row 0 │[0] 0  0  0  0  0  0  0  …
row 1 │ 1 [0] 0  0  0  0  0  0  …
row 2 │ 0  1 [0] 0  0  0  0  0  …
row 3 │ 1  1  0 [0] 0  0  0  0  …
row 4 │ 0  0  1  0 [0] 0  0  0  …
row 5 │ 1  0  1  0  0 [0] 0  0  …
row 6 │ 0  1  1  0  0  0 [0] 0  …
row 7 │ 1  1  1  0  0  0  0 [0] …
──────┼──────────────────────────
flip  │ 1  1  1  1  1  1  1  1  …
```

(Row `n` is `n` in binary, lowest bit first. The file prints this picture with `#eval`.)

## What is proved

In [`Cantor/Diagonal.lean`](Cantor/Diagonal.lean), with core Lean only (no Mathlib):

| Theorem | Statement |
|---|---|
| `Cantor.diagonal_ne` | the flipped diagonal is not row `n`, for every `n` |
| `Cantor.not_surjective` | no list `f : Nat → (Nat → Bool)` contains every binary sequence |
| `Cantor.uncountable` | nothing maps `Nat` onto the binary sequences |
| `Cantor.cantor` | for any type `α`, no `f : α → (α → Prop)` reaches every subset of `α` |

None of them depends on any axiom (`#print axioms` lists none): not `propext`, not `Classical.choice`.

## Build

```
lake build
```

Lean 4.34.0 (see `lean-toolchain`). Written and checked in [Lean Studio](https://github.com/keithadler/leanstudio).
