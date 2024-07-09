import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.IsROrC.Basic

import EspaciosHilbert.definiciones
import EspaciosHilbert.lemas
import EspaciosHilbert.cauchyschwarz
import EspaciosHilbert.normainducida
import EspaciosHilbert.metricainducida

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)


namespace riesz

variable {𝕜 : Type*} [IsROrC 𝕜] [HilbertSpace 𝕜 𝕜]
variable {F : Type*} [AddCommGroup F] [HilbertSpace 𝕜 F]

export InnerProductSpace (prod_esc_ref_pos)
export InnerProductSpace (mult_por_esc)
export InnerProductSpace (conj_symm)
export InnerProductSpace (prod_esc_cero_1)
export InnerProductSpace (prod_esc_cero_2)
export IsBoundedLinearMap (bound)
export IsLinearMap (map_add)
export IsLinearMap (map_sub)
export IsLinearMap (map_smul)

axiom func_lineal (f : F → 𝕜) (x : F) (a : 𝕜) (lineal: IsLinearMap 𝕜 f)
[InnerProductSpace 𝕜 𝕜] : f (a • x) = a * f x


axiom teorema_proyeccion (x : F) (f : F → 𝕜) (la : IsBoundedLinearMap 𝕜 f) : ∃ y : F, (f y = 0) ∧ ∀ z : F,
  f z = 0 → @norma_inducida 𝕜 F _ _ _ (x - y) ≤ @norma_inducida 𝕜 F _ _ _ (x - z)


theorem proyeccion_ortogonal (x y : F) (f : F → 𝕜) (la : IsBoundedLinearMap 𝕜 f)  (h1 : f y = 0)
  (h2 : ∀ z : F, f z = 0 → @norma_inducida 𝕜 F _ _ _ (x - y) ≤ @norma_inducida 𝕜 F _ _ _ (x - z)):
  ∀ z : F, f z = 0 → @inner 𝕜 F _ z (x - y) = 0 := by
  by_contra h3
  push_neg at h3
  obtain ⟨z,h4⟩ := h3
  obtain ⟨h4,h5⟩ := h4
  by_cases h6 : z = 0
-- Caso z = 0
  have contra : @inner 𝕜 F _ z (x-y) = 0 := by
    rw[h6, producto_cero_l]
  contradiction
-- Caso z ≠ 0
  let lineal := la.toIsLinearMap
  have h7 : ∀ a : 𝕜, f (y + a•z) = 0 := by
    intro a
    rw[map_add lineal, map_smul lineal, h1, h4, @smul_zero 𝕜, zero_add]
  have h8 : @inner 𝕜 F _ z z ≠ 0 := by
    by_contra h9
    apply prod_esc_cero_1 at h9
    contradiction
  have contra : @norma_inducida 𝕜 F _ _ _ (x - (y + (@inner 𝕜 F _ (x-y) z/
  (@inner 𝕜 F _ z z)) • z))^2 < @norma_inducida 𝕜 F _ _ _ (x - y)^2:= by
    unfold norma_inducida
    rw[sub_add_eq_sub_sub, lema_dcs, conj_div, ← conj_symm z (x-y), ← conj_symm z z, div_mul_cancel, sub_self,
    mul_zero, sub_zero, div_mul_eq_mul_div, conj_symm (x-y) z, sq_sqrt, sq_sqrt, AddMonoidHom.map_sub,
    ← re_add_im (@inner 𝕜 F _ z z), prod_esc_ref_pos.right, ofReal_zero, zero_mul, add_zero, div_re_ofReal]
    have i1 : 0 < re (@inner 𝕜 F _ z (x-y) * conj (@inner 𝕜 F _ z (x-y))) / (re (@inner 𝕜 F _ z z)) := by
      have i2 : 0 ≤ re (@inner 𝕜 F _ z (x-y) * conj (@inner 𝕜 F _ z (x-y))) := by
        exact (@modulo_pos 𝕜 _ (@inner 𝕜 F _ z (x-y)))
      have i3 : 0 ≠ re (@inner 𝕜 F _ z (x-y) * conj (@inner 𝕜 F _ z (x-y))) := by
        by_contra h
        simp at h
        rw[← pow_two, ← pow_two] at h
        apply lema_ab2 at h
        obtain ⟨i1,i2⟩ := h
        apply (re_im_cero i1) at i2
        contradiction
      have i4 : 0 < re (@inner 𝕜 F _ z (x-y) * conj (@inner 𝕜 F _ z (x-y))) := by
        exact lt_of_le_of_ne i2 i3
      have i5 : 0 < re (@inner 𝕜 F _ z z) := by
        have i6 : 0 ≤ re (@inner 𝕜 F _ z z) := by
          exact prod_esc_ref_pos.left
        have i7 : 0 ≠ re (@inner 𝕜 F _ z z) := by
          rw[← re_add_im (@inner 𝕜 F _ z z), prod_esc_ref_pos.right, ne_comm] at h8
          simp at h8
          rw[← ofReal_zero, ofReal_inj] at h8
          push_neg at h8
          exact h8
        exact lt_of_le_of_ne i6 i7
      exact (div_pos_iff_of_pos_left i4).mpr i5
    exact sub_lt_self (re (@inner 𝕜 F _ (x-y) (x-y))) i1
    exact prod_esc_ref_pos.left
    have h9 : ∀ a : 𝕜, 0 ≤ re (@inner 𝕜 F _ (x - y - a • z) (x - y - a • z)) := by
      intro a
      exact prod_esc_ref_pos.left
    specialize h9 ((@inner 𝕜 F _ (x-y) z) / (@inner 𝕜 F _ z z))
    rw [lema_dcs, conj_div, ← conj_symm z (x-y), ← conj_symm z z, div_mul_cancel, sub_self,
    mul_zero, sub_zero, div_mul_eq_mul_div, conj_symm (x-y) z] at h9
    exact h9
    exact h8
    exact h8
  specialize h2 (y + (@inner 𝕜 F _ (x-y) z/ (@inner 𝕜 F _ z z)) • z)
  specialize h7 (@inner 𝕜 F _ (x-y) z/ (@inner 𝕜 F _ z z))
  apply h2 at h7
  apply pow_le_pow_left at h7
  specialize h7 2
  apply (not_lt.mpr) at h7
  contradiction
  let h := @norma_inducida_pos 𝕜 F
  unfold norma_pos at h
  specialize h (x-y)
  exact h


theorem suma_directa (f : F → 𝕜) (la : IsBoundedLinearMap 𝕜 f)
(x : F) (h : f x ≠ 0) : ∃ y z : F, f y = 0 ∧ f z ≠ 0 ∧
∀ t : F, (f t = 0 → @inner 𝕜 F _ t z = 0) := by
  let h1 := (@teorema_proyeccion 𝕜 _ _ F _ _ x f la)
  obtain ⟨y, h1⟩ := h1
  use y
  use x-y
  constructor
  exact h1.left
  constructor
  rw[map_sub la.toIsLinearMap, h1.left, sub_zero]
  exact h
  exact (proyeccion_ortogonal x y f la h1.left h1.right)


-- Teorema de Representación de Riesz
theorem riesz (f : F → 𝕜) (linealacotada : IsBoundedLinearMap 𝕜 f) :
∃ z : F, ∀ x : F, f x = (@inner 𝕜 F _ x z) := by
  by_cases h : ∀ x : F, f x = 0
-- Caso f = 0
  use 0
  intro x
  rw [producto_cero_r]
  specialize h x
  exact h

-- Caso f ≠ 0
  push_neg at h
  let lineal := linealacotada.toIsLinearMap
  obtain ⟨x, h⟩ := h
  let h1 := suma_directa f linealacotada x h
  obtain ⟨y,h1⟩ := h1
  obtain ⟨z,h1⟩ := h1
  obtain ⟨_,h2⟩ := h1
  obtain ⟨h2,h3⟩ := h2
  use (((conj (f z)) / (inner z z)) • z)
  intro x
  rw[conj_symm, mult_por_esc, map_mul conj, conj_symm z z, ← IsROrC.conj_div, starRingEnd_self_apply,
  ← conj_symm]
  have h2 : @inner 𝕜 F _ z z ≠ 0 := by
    by_contra neg
    apply prod_esc_cero_1 at neg
    have h3 : f z = 0 := by
      rw[neg, IsLinearMap.map_zero lineal]
    contradiction
  rw[← mul_left_inj' h2, mul_right_comm, div_mul_cancel _ h2]
  have h : f ((f x) • z - (f z) • x) = 0 := by
    rw[@map_sub 𝕜 F 𝕜 _ _ _ _ _ f lineal, @func_lineal 𝕜 _ _ F _ _ f z (f x) lineal,
    @func_lineal 𝕜 _ _ F _ _ f x (f z) lineal, @mul_comm 𝕜, sub_self]
  specialize h3 ((f x) • z - (f z) • x)
  apply h3 at h
  rw[linealidad_menos, @mult_por_esc 𝕜, @mult_por_esc 𝕜, sub_eq_zero] at h
  exact h


theorem unicidad_riesz (f : F → 𝕜) (z1 z2 : F) (h1 : ∀ x : F, f x = (@inner 𝕜 F _ x z1))
(h2 : ∀ x : F, f x = (@inner 𝕜 F _ x z2)) : z1 = z2 := by
  specialize h1 (z1 - z2)
  specialize h2 (z1 - z2)
  rw[h1] at h2
  apply sub_eq_zero_of_eq at h2
  rw[conj_symm, conj_symm (z1-z2) z2, ← RingHom.map_sub, ← linealidad_menos, ← conj_symm] at h2
  apply prod_esc_cero_1 at h2
  rw[sub_eq_zero] at h2
  exact h2

end riesz
