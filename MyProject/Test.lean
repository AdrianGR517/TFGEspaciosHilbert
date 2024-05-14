import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.NormedSpace.Completion
import Mathlib.Analysis.NormedSpace.IsROrC
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Data.IsROrC.Basic

def doble (x : ℕ) : ℕ :=
  2 * x

theorem ejemplo8 (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by
  intro h
  have h3 : q := by
    apply h1 h
  apply h2 h3

theorem ejemplo4 (p q : Prop) (h1 : p → q) (h2 : p) : q := by
  apply h1 h2

theorem ejemplo5 (p q : Prop) (h1 : p) (h2 : q) : p ∧ q := by
  constructor
  exact h1
  exact h2

theorem ejemplo7 (p q : Prop) (h : p) : p ∨ q := by
  left
  exact h

theorem ejemplo9 (a b : ℤ) (h : ∃ c, a + c = 0) : ∃ c, (a + b) + c = b := by
  obtain ⟨z, h1⟩ := h
  use z
  rw[add_comm, ← add_assoc, add_comm z a, h1, zero_add]

theorem ejemplo10 (p q : Prop) (h : (¬ p) ∨ q) : p → q := by
  intro h1
  cases h with
  | inl h2 =>
    exfalso
    contradiction
  | inr h2 =>
    exact h2

theorem ejemplo11 (p : Type* → Prop) (h : ∃ x, (¬ p x)) : ¬ ∀ x, p x := by
  by_contra h1
  obtain ⟨z, h2⟩ := h
  specialize h1 z
  contradiction
