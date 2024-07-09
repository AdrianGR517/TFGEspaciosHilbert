import Mathlib.Data.IsROrC.Basic

class GrupoConmutativo (A : Type) extends AddGroup A where
  conmutatividad : ∀ a b : A, a + b = b + a

def doble' {A : Type} [AddCommGroup A] (x : A) : A :=
  x + x

def opuesto {A : Type} [AddGroup A] (x y : A) : Prop :=
  x + y = 0

theorem ejemplo1 (a b : ℕ) : 0 + a + b = a + b := by
    rw [zero_add]

theorem ejemplo2 (a : ℕ) (h : a = 0) : a = 0 := by
    exact h

def doble (n : ℕ) : ℕ :=
    2 * n

theorem ejemplo3 (x y : ℕ) : doble (x + y) = doble x + doble y := by
    unfold doble
    rw [mul_add]

theorem ejemplo4 (p q : Prop) (h1 : p → q) (h2 : p) : q := by
  apply h1 h2

theorem ejemplo5 (p q : Prop) (h1 : p) (h2 : q) : p ∧ q := by
  constructor
  exact h1
  exact h2

theorem ejemplo6 (a : ℤ) : ∃ b, a + b = 0 := by
    use (- a)
    simp

theorem ejemplo7 (p q : Prop) (h : p) : p ∨ q := by
  left
  exact h

theorem ejemplo8 (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by
  intro h
  have h3 : q := by
    apply h1 h
  apply h2 h3

theorem ejemplo9 (a b : ℤ) (h : ∃ c, a + c = 0) : ∃ c, (a + b) + c = b := by
  obtain ⟨z, h1⟩ := h
  use z
  rw[add_comm,← add_assoc,add_comm z a,h1,zero_add]

theorem ejemplo10 (p : Type → Prop) (a : Type) (h : ∀ x, p x) : p a := by
  specialize h a
  exact h

theorem ejemplo11 (p q : Prop) (h : (¬ p) ∨ q) : p → q := by
  intro h1
  cases h with
  | inl h2 =>
    exfalso
    contradiction
  | inr h2 =>
    exact h2

theorem ejemplo12 (p q r : Prop) (h1 : p → q) (h2 : p ∨ r) (h3 : ¬ p → ¬ r) : q := by
  by_contra h4
  have h5 : ¬ p := by
    by_contra h6
    apply h1 at h6
    contradiction
  cases h2 with
  | inl h =>
    contradiction
  | inr h =>
    apply h3 at h5
    contradiction
