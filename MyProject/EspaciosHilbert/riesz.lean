import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.NormedSpace.Completion
import Mathlib.Analysis.NormedSpace.IsROrC
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Data.IsROrC.Basic

import MyProject.EspaciosHilbert.definiciones
import MyProject.EspaciosHilbert.lemmas

open BigOperators Topology ComplexConjugate

namespace riesz

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {F : Type*} [AddCommGroup F] [InnerProductSpace 𝕜 F]

export InnerProductSpace (mult_por_esc)
export InnerProductSpace (conj_symm)
export InnerProductSpace (prod_esc_cero_2)

lemma producto_cero {x : F} : @inner 𝕜 F _ 0 x = (0 : 𝕜) := by
  have h : ∀ a : F, (0 : 𝕜) • a = (0 : F) := by
    intro a
    rw [zero_smul]
  specialize h x
  rw [← h]
  have h2 : ∀ a : 𝕜, (0 : 𝕜) * a = (0 : 𝕜) := by
    intro a
    simp
  specialize h2 (@inner 𝕜 F _ x x)
  rw [← h2]
  rw [mult_por_esc]
  simp

lemma producto_cero_r {x : F} : @inner 𝕜 F _ x 0 = 0 := by
  rw [conj_symm]
  have h : ∀ a : F, (0 : 𝕜) • a = 0 := by
    intro a
    rw [zero_smul]
  specialize h x
  rw [producto_cero]
  simp


theorem riesz_base {f:F → 𝕜} : ∃ z : F, ∀ x : F, f x = inner x z := by
  by_cases h : ∀ x : F, f x = 0
-- Caso f = 0
  use 0
  intro x
  rw [producto_cero_r]
  specialize h x
  exact h

-- Caso f ≠ 0
  push_neg at h
  obtain ⟨z, h1⟩ := h
  use (((conj (f z)) / (inner z z)) • z)
  intro x

  sorry


end riesz
