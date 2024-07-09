import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.IsROrC.Basic

import EspaciosHilbert.definiciones

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)

noncomputable section

variable {𝕜 : Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E]

export IsROrC (norm_sq_eq_def_ax)
export IsROrC (re_add_im_ax)

-- Lemas previos para probar que la norma inducida es lineal
export InnerProductSpace (prod_esc_ref_pos)
export InnerProductSpace (mult_por_esc)
export InnerProductSpace (prod_esc_cero_1)
export InnerProductSpace (prod_esc_cero_2)
export InnerProductSpace (conj_symm)
export InnerProductSpace (linealidad)

-- El módulo al cuadrado es positivo
lemma modulo_pos (a : 𝕜) : 0 ≤ re (a * (conj a)):= by
  simp
  rw[← pow_two, ← pow_two]
  have i1 : 0 ≤ re a ^2 := by
    exact sq_nonneg (re a)
  have i2 : 0 ≤ im a ^2 := by
    exact sq_nonneg (im a)
  linarith

-- Si la parte real y la parte imaginaria son cero entonces el complejo es cero
lemma re_im_cero {x : 𝕜} (rezero : re x = 0)  (imzero : im x = 0) : x = 0 := by
  rw[← re_add_im x, rezero, imzero]
  simp

-- ‖a•x‖ = |a|²*‖x‖
lemma lema_norma_lineal (a : 𝕜) (x : E) :
  re (@inner 𝕜 E _ (a • x) (a • x)) = ((modulo a)^2) * re (@inner 𝕜 E _ x x) := by
  rw [mult_por_esc,conj_symm,mult_por_esc,conj_symm]
  unfold modulo
  rw [sq_sqrt]
  have h1 : im (@inner 𝕜 E _ x x) = 0 := by
    exact prod_esc_ref_pos.right
  rw[map_mul conj, ← mul_assoc, mul_re_ax, ← conj_symm, ← conj_symm, h1, mul_zero, sub_zero]
  exact modulo_pos a

-- La parte real es menor o igual que el módulo
lemma lema_dt1 (a : 𝕜) : re a ≤ modulo a := by
  by_cases h : 0 ≤ re a
  -- Caso 0 ≤ re a
  unfold modulo
  simp
  rw[← pow_two, ← pow_two, ← sqrt_sq h, sqrt_le_sqrt_iff, sqrt_sq h, le_add_iff_nonneg_right]
  exact (sq_nonneg (im a))
  have i1 : 0 ≤ sqrt (re a ^ 2) ^ 2 := by
    exact sq_nonneg (sqrt (re a ^ 2))
  have i2 : 0 ≤ im a ^ 2 := by
    exact sq_nonneg (im a)
  linarith
  -- Caso re a < 0
  push_neg at h
  have ineq1 : 0 ≤ modulo a := by
    unfold modulo
    exact sqrt_nonneg (re (a * (starRingEnd 𝕜) a))
  linarith

-- Desarrollo de ⟨a + b, a + b⟩
lemma lema_dt2 (a b : E) : @inner 𝕜 E _ (a + b) (a + b) =
  inner a a + inner b b + 2 * re (@inner 𝕜 E _ a b) := by
  rw[linealidad, conj_symm, conj_symm b, linealidad, linealidad, map_add conj, map_add conj,
  ← conj_symm, ← conj_symm, ← conj_symm b b, ← add_assoc, add_assoc (inner a a), add_conj, add_right_comm]


-- El producto de 0 y cualquier cosa es 0
lemma producto_cero_l {x : E} : @inner 𝕜 E _ 0 x = (0 : 𝕜) := by
  rw[← @zero_smul 𝕜 E _ _ _ x, mult_por_esc, zero_mul]

-- El producto de cualquier cosa y 0 es 0
lemma producto_cero_r {x : E} : @inner 𝕜 E _ x 0 = 0 := by
  rw [conj_symm, producto_cero_l, map_zero conj]

-- ⟨a-b, c⟩ = ⟨a, c⟩ - ⟨b, c⟩
lemma linealidad_menos (a b c : E) : inner (a - b) c = @inner 𝕜 E _ a c - inner b c := by
  rw[sub_eq_add_neg a b, linealidad, ← @neg_one_smul 𝕜 E _ _ _ b, mult_por_esc, neg_one_mul,
  ← sub_eq_add_neg]


lemma lema_dcs (a : 𝕜) (f g : E) : @inner 𝕜 E _ (f - a • g) (f - a • g) =
  inner f f - conj a * inner f g - a * (inner g f - conj a * inner g g):= by
  rw[linealidad_menos, mult_por_esc, conj_symm, conj_symm g, linealidad_menos, linealidad_menos,
  mult_por_esc, mult_por_esc, map_sub (starRingEnd 𝕜), map_sub (starRingEnd 𝕜),
  ← conj_symm, map_mul conj, ← conj_symm, ← conj_symm, map_mul conj,
  ← conj_symm]

lemma lema_re (a b c : 𝕜) (h1 : im c = 0) (h2 : 0 < re c) :
  re (a) ≤ re (b) ↔ re (a * c) ≤ re (b * c) := by
  simp
  rw[h1]
  simp
  rw[mul_le_mul_iff_of_pos_right]
  exact h2

lemma lema_ab2 (a b : ℝ) (h : 0 = a^2 + b^2) : a = 0 ∧ b = 0 := by
  have i1 : 0 ≤ a^2 := by
    exact sq_nonneg a
  have i2 : 0 ≤ b^2 := by
    exact sq_nonneg b
  by_contra h1
  push_neg at h1
  by_cases h2 : a = 0
  apply h1 at h2
  have i3 : 0 < b^2 := by
    by_contra i4
    push_neg at i4
    have b0 : b^2 = 0 := by
      linarith
    rw[sq_eq_zero_iff] at b0
    contradiction
  apply Right.add_pos_of_pos_of_nonneg i3 at i1
  apply ne_of_lt at i1
  rw[add_comm] at i1
  contradiction
  have i3 : 0 < a^2 := by
    by_contra i4
    push_neg at i4
    have a0 : a^2 = 0 := by
      linarith
    rw[sq_eq_zero_iff] at a0
    contradiction
  apply Right.add_pos_of_pos_of_nonneg i3 at i2
  apply ne_of_lt at i2
  contradiction
