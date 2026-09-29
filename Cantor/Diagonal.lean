/-!
# Cantor's diagonal argument

List infinite binary sequences one per row: `f 0`, `f 1`, `f 2`, … Walk down the diagonal and flip each
bit. The sequence you get differs from row `n` at position `n`, so it is on no row: no list, however
long, contains every binary sequence. There are more of them than there are natural numbers.

The same step, "flip what `a` says about itself", proves Cantor's theorem for any type: no `α` maps
onto its own subsets `α → Prop`.

Core Lean only, no Mathlib.
-/

namespace Cantor

/-- An infinite binary sequence (a point of Cantor space): bit `k` is `s k`. -/
abbrev Seq := Nat → Bool

/-- The diagonal of the list `f`, flipped: bit `n` is the opposite of bit `n` of row `n`. -/
def diagonal (f : Nat → Seq) : Seq := fun n => !(f n n)

/-- The flipped diagonal disagrees with row `n` at position `n`. -/
theorem diagonal_differs (f : Nat → Seq) (n : Nat) : diagonal f n ≠ f n n := by
  unfold diagonal
  cases f n n <;> decide

/-- So it is not row `n`, for any `n`. -/
theorem diagonal_ne (f : Nat → Seq) (n : Nat) : f n ≠ diagonal f := by
  intro h
  exact diagonal_differs f n (congrFun h n).symm

/-- **Cantor's diagonal argument.** No list of binary sequences contains them all. -/
theorem not_surjective (f : Nat → Seq) : ∃ s : Seq, ∀ n, f n ≠ s :=
  ⟨diagonal f, diagonal_ne f⟩

/-- The binary sequences cannot be counted: nothing maps `Nat` onto them. -/
theorem uncountable : ¬ ∃ f : Nat → Seq, ∀ s, ∃ n, f n = s := by
  intro ⟨f, onto⟩
  obtain ⟨n, h⟩ := onto (diagonal f)
  exact diagonal_ne f n h

/-- **Cantor's theorem**, the same argument for any type: no `α` maps onto its subsets. -/
theorem cantor {α : Type u} (f : α → α → Prop) : ∃ s : α → Prop, ∀ a, f a ≠ s := by
  refine ⟨fun a => ¬ f a a, fun a h => ?_⟩
  have e : f a a = ¬ f a a := congrFun h a
  have no : ¬ f a a := fun yes => (e ▸ yes) yes
  exact no (e ▸ no)

/-! ## Seeing it

A concrete list: row `n` is the binary digits of `n`, lowest first (`5 = 101₂` gives `1 0 1 0 0 …`). It
has every sequence with finitely many ones, yet the diagonal flips it to all ones, which is on no row. -/

/-- Row `n`: the binary digits of `n`, lowest first. -/
def binary : Nat → Seq := fun n k => (n >>> k) % 2 == 1

example : binary 5 0 = true ∧ binary 5 1 = false ∧ binary 5 2 = true := by decide

/-- Bit `n` of `n` is always 0 (`n < 2 ^ n`), so the flipped diagonal of this list is all ones. -/
example : (List.range 16).all (fun n => diagonal binary n) = true := by decide

/-- And all ones is on no row, by the theorem. -/
example (n : Nat) : binary n ≠ diagonal binary := diagonal_ne binary n

/-- The first `size` rows and columns of `f`, the diagonal in brackets, and the flipped diagonal below. -/
def picture (f : Nat → Seq) (size : Nat := 8) : String :=
  let bit (b : Bool) := if b then "1" else "0"
  let cell (n k : Nat) := if n == k then s!"[{bit (f n k)}]" else s!" {bit (f n k)} "
  let row (n : Nat) := s!"row {n} │" ++ String.join ((List.range size).map (cell n)) ++ " …"
  let flipped := "flip  │" ++ String.join ((List.range size).map fun k => s!" {bit (diagonal f k)} ") ++ " …"
  "\n".intercalate ((List.range size).map row ++ ["──────┼" ++ "".pushn '─' (3 * size + 2), flipped])

#eval IO.println (picture binary)

end Cantor
