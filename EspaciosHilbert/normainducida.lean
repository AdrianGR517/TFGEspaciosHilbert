import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.IsROrC.Basic

import EspaciosHilbert.definiciones
import EspaciosHilbert.lemas
import EspaciosHilbert.cauchyschwarz

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)

noncomputable section

variable {𝕜 :Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E]

-- ‖x‖ ≥ 0
def norma_pos (E : Type*) (norma : E → ℝ) : Prop :=
  ∀ x : E, 0 ≤ norma x

theorem norma_inducida_pos : norma_pos E (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_pos
  unfold norma_inducida
  intro x
  exact (sqrt_nonneg (re (inner x x)))


-- ‖x‖ = 0 ↔ x = 0
def norma_cero (E : Type*) (norma : E → ℝ) [OfNat E 0]: Prop :=
  ∀ x : E, norma (x) = 0 ↔ x = (0 : E)

theorem norma_inducida_cero : norma_cero E (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_cero
  intro x
  unfold norma_inducida
  constructor
-- →
  intro h1
  rw [Real.sqrt_eq_zero] at h1
  have h2 : im (inner x x) = 0 := by
    exact (@InnerProductSpace.prod_esc_ref_pos 𝕜 E _ _ _ x).right
  have h : @inner 𝕜 E _ x x = 0 := by
    exact re_im_cero h1 h2
  apply prod_esc_cero_1 h
  exact prod_esc_ref_pos.left
-- ←
  intro h
  rw[h, producto_cero_l,zero_re',sqrt_zero]

-- ‖a • x‖ = |a| * ‖x‖
def norma_lineal (E : Type*) [AddCommGroup E] [Module 𝕜 E] (norma : E → ℝ) : Prop :=
  ∀ a : 𝕜, ∀ x : E, norma (a • x) = (modulo a) * (norma x)

theorem norma_inducida_lineal : @norma_lineal 𝕜 _ E _ _ (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_lineal
  intro a x
  unfold norma_inducida
  rw [lema_norma_lineal, sqrt_mul (sq_nonneg (modulo a)), sqrt_sq]
  unfold modulo
  exact sqrt_nonneg (re (a * (starRingEnd 𝕜) a))

-- ‖a + b‖ ≤ ‖a‖ + ‖b‖
def norma_des_triang (E : Type*) [AddCommGroup E] [Module 𝕜 E] (norma : E → ℝ) : Prop :=
  ∀ a b : E, norma (a + b) ≤ norma (a) + norma (b)

theorem norma_inducida_des_triang : @norma_des_triang 𝕜 _ E _ _ (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_des_triang
  intro a b
  unfold norma_inducida
  rw[lema_dt2]
  have ineq1 : sqrt (re (@inner 𝕜 E _ a a + inner b b + 2 * ↑(re (@inner 𝕜 E _ a b)))) ≤
  sqrt (re (@inner 𝕜 E _ a a + inner b b + 2 * ↑((modulo (@inner 𝕜 E _ a b))))) := by
    rw[map_add re, map_add re, map_add re, map_add re, two_mul, map_add re, ofReal_re,
    two_mul, map_add re, ofReal_re, ← two_mul, ← two_mul]
    have ineq1_1 : re (@inner 𝕜 E _ a a) + re (@inner 𝕜 E _ b b) + 2 * re (@inner 𝕜 E _ a b) ≤
    re (@inner 𝕜 E _ a a) + re (@inner 𝕜 E _ b b) + 2 * modulo (@inner 𝕜 E _ a b) := by
      simp
      exact lema_dt1 (inner a b)
    exact sqrt_le_sqrt ineq1_1
  have ineq2 : sqrt (re (@inner 𝕜 E _ a a + inner b b + 2 * ↑(modulo (@inner 𝕜 E _ a b)))) ≤
  sqrt (re (@inner 𝕜 E _ a a) + re (@inner 𝕜 E _ b b) +
  2 * sqrt (re (@inner 𝕜 E _ a a)) * sqrt (re (@inner 𝕜 E _ b b))) := by
    have ineq2_1 : re (@inner 𝕜 E _ a a + inner b b + 2 * ↑(modulo (@inner 𝕜 E _ a b))) ≤
    re (@inner 𝕜 E _ a a) + re (@inner 𝕜 E _ b b) +
    2 * sqrt (re (@inner 𝕜 E _ a a)) * sqrt (re (@inner 𝕜 E _ b b)) := by
      simp
      rw[mul_assoc, mul_le_mul_left]
      exact @cauchyschwarz.des_cauchy_schwartz_mod 𝕜 E _ _ _ a b
      exact zero_lt_two
    exact sqrt_le_sqrt ineq2_1
  have eq1 : sqrt (re (@inner 𝕜 E _ a a) + re (@inner 𝕜 E _ b b) +
  2 * sqrt (re (@inner 𝕜 E _ a a)) * sqrt (re (@inner 𝕜 E _ b b))) =
  sqrt (re (@inner 𝕜 E _ a a)) + sqrt (re (@inner 𝕜 E _ b b)) := by
    have h1 : 0 ≤ re (inner a a) := by
      exact (@prod_esc_ref_pos 𝕜 E _ _ _ a).left
    have h2 : 0 ≤ re (inner b b) := by
      exact (@prod_esc_ref_pos 𝕜 E _ _ _ b).left
    rw[← sq_sqrt h1, ← sq_sqrt h2, sqrt_sq, sqrt_sq, ← add_sq', sqrt_sq]
    apply add_nonneg
    exact sqrt_nonneg (re (inner a a))
    exact sqrt_nonneg (re (inner b b))
    exact sqrt_nonneg (re (inner b b))
    exact sqrt_nonneg (re (inner a a))
  linarith
