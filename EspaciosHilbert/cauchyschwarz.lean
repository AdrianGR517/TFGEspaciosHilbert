import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.IsROrC.Basic

import EspaciosHilbert.definiciones
import EspaciosHilbert.lemas

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)

namespace cauchyschwarz

variable {𝕜 :Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E]

export InnerProductSpace (prod_esc_ref_pos)
export InnerProductSpace (mult_por_esc)
export InnerProductSpace (prod_esc_cero_1)
export InnerProductSpace (conj_symm)

theorem des_cauchy_schwartz (f g : E) : modulo (@inner 𝕜 E _ f g) ^ 2 ≤
re ((@inner 𝕜 E _ f f) * (@inner 𝕜 E _ g g)) := by
  by_cases h : g = (0 : E)
  rw[h, producto_cero_r, producto_cero_r]
  unfold modulo
  simp

  have h2 : ∀ a : 𝕜, re (@inner 𝕜 E _ (f - a • g) (f - a • g)) ≥ 0 := by
    intro a
    exact prod_esc_ref_pos.left
  have h3 : (@inner 𝕜 E _ g g) ≠ 0 := by
    by_contra contra
    apply prod_esc_cero_1 at contra
    contradiction
  have h4 : re (@inner 𝕜 E _ g g) ≠ 0 := by
    by_contra c
    have h5 : im (@inner 𝕜 E _ g g) = 0 := by
      exact prod_esc_ref_pos.right
    have h6 : @inner 𝕜 E _ g g = 0 := by
      exact @re_im_cero 𝕜 _ (@inner 𝕜 E _ g g) c h5
    contradiction
  specialize h2 ((inner f g)/(inner g g))
  have h1 : re (@inner 𝕜 E _ g g) ≥ 0 := by
    exact prod_esc_ref_pos.left
  have i1 : ((@inner 𝕜 E _ f g)/(inner g g)) = conj ((inner g f)/(inner g g)) := by
    rw[conj_symm, conj_symm g g, conj_div, ← conj_symm g g, ← conj_symm g g]
  rw[lema_dcs, i1, starRingEnd_self_apply, div_mul_cancel,
  @sub_eq_zero_of_eq 𝕜 _ (@inner 𝕜 E _ g f), @mul_zero 𝕜 _, @sub_zero 𝕜 _,
  @AddMonoidHom.map_sub 𝕜 ℝ _ _ re, ge_iff_le, sub_nonneg, lema_re _ _ (inner g g),
  mul_right_comm, div_mul_cancel] at h2
  unfold modulo
  rw[sq_sqrt, ← conj_symm, mul_comm (inner f g)]
  exact h2
  exact (@modulo_pos 𝕜 _ (inner f g))
  exact h3
  exact prod_esc_ref_pos.right
  apply (@Ne.symm ℝ (re (@inner 𝕜 E _ g g)) 0) at h4
  exact lt_of_le_of_ne h1 h4
  rfl
  exact h3

-- Variante de Cauchy-Schwarz
theorem des_cauchy_schwartz_mod (f g : E) : modulo (@inner 𝕜 E _ f g) ≤
sqrt (re (@inner 𝕜 E _ f f)) * sqrt (re (@inner 𝕜 E _ g g)) := by
  unfold modulo
  rw[← sqrt_mul', sqrt_le_sqrt_iff]
  have eq1 : re (@inner 𝕜 E _ f g * conj (inner f g)) = (modulo (@inner 𝕜 E _ f g))^2 := by
    unfold modulo
    rw[sq_sqrt]
    exact modulo_pos (inner f g)
  rw[eq1, ← sub_zero (re (inner f f) * re (inner g g))]
  have eq2 : 0 = im (@inner 𝕜 E _ f f) * im (@inner 𝕜 E _ g g) := by
    rw[(@prod_esc_ref_pos 𝕜 E _ _ _ f).right,(@prod_esc_ref_pos 𝕜 E _ _ _ g).right, zero_mul]
  rw[eq2, ← mul_re_ax]
  exact (@des_cauchy_schwartz 𝕜 E _ _ _ f g)
  let h1 := (@prod_esc_ref_pos 𝕜 E _ _ _ f).left
  let h2 := (@prod_esc_ref_pos 𝕜 E _ _ _ g).left
  exact mul_nonneg h1 h2
  exact (@prod_esc_ref_pos 𝕜 E _ _ _ g).left

end cauchyschwarz
