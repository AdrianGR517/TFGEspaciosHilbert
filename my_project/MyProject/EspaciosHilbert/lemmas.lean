import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.NormedSpace.Completion
import Mathlib.Analysis.NormedSpace.IsROrC
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Data.IsROrC.Basic
import MyProject.EspaciosHilbert.definiciones

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)

noncomputable section

namespace normaprodesc

variable {𝕜 :Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E]

-- Definimos la norma inducida por el producto escalar
def norma_inducida [InnerProductSpace 𝕜 E] (x : E) : ℝ :=
  sqrt (re (@inner 𝕜 E _ x x))

-- Vemos que cumple la primera propiedad
theorem norma_inducida_pos : norma_pos E (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_pos
  unfold norma_inducida
  intro x
  simp
  exact (sqrt_nonneg (re (inner x x)))

-- Lema previo que dice que x es 0 si y solo si sus partes real e imaginaria lo son
export IsROrC (norm_sq_eq_def_ax)
export IsROrC (re_add_im_ax)

lemma re_im_cero {x : 𝕜} : (re x = 0 ∧ im x = 0) ↔ x = 0 := by
  constructor
  intro h
  have h1 : re x = 0 := by
    linarith
  have h2 : im x = 0 := by
    linarith
  rw[← re_add_im x, h1, h2]
  simp

  intro h
  constructor
  rw [h]
  simp
  rw [h]
  simp

export InnerProductSpace (prod_esc_cero_1)
export InnerProductSpace (prod_esc_cero_2)

-- La norma inducida es 0 si y solo si x es 0
theorem norma_inducida_cero : norma_cero E (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_cero
  intro x
  unfold norma_inducida
  constructor
  intro h
  rw [Real.sqrt_eq_zero] at h
  have h1 : re (inner x x) ≥ 0 ∧ im (inner x x) = 0 := by
    exact (@InnerProductSpace.prod_esc_sim_pos 𝕜 E _ _ _ x)
  have h2 : im (inner x x) = 0 := by
    linarith
  have h3 : re (inner x x) = 0 ∧ im (inner x x) = 0 := by
    constructor
    exact h
    exact h2
  have h4 : (@inner 𝕜 E _ x x) = 0 := by
    rw [← re_im_cero]
    exact h3
  exact @prod_esc_cero_1 𝕜 E _ _ _ x h4
  have h1 : re (inner x x) ≥ 0 ∧ im (inner x x) = 0 := by
    exact (@InnerProductSpace.prod_esc_sim_pos 𝕜 E _ _ _ x)
  have h2 : 0 ≤ re (inner x x) := by
    linarith
  exact h2
  intro h
  rw [h, prod_esc_cero_2]
  simp

-- Lemas previos para probar que la norma inducida es lineal
export InnerProductSpace (prod_esc_sim_pos)
export InnerProductSpace (mult_por_esc)
export InnerProductSpace (conj_symm)
export InnerProductSpace (linearidad)

lemma lema_norma_lineal {a : 𝕜} {x : E} :
  re (@inner 𝕜 E _ (a • x) (a • x)) = ((modulo a)^2) * re (@inner 𝕜 E _ x x) := by
  rw [mult_por_esc,conj_symm,mult_por_esc,conj_symm]
  unfold modulo
  rw [sq_sqrt]
  have h1 : im (@inner 𝕜 E _ x x) = 0 := by
    have h2 : re (@inner 𝕜 E _ x x) ≥ 0 ∧ im (@inner 𝕜 E _ x x) = 0 := by
      exact prod_esc_sim_pos
    obtain ⟨_ , h4⟩ := h2
    exact h4
  simp
  rw [h1]
  simp
  rw [add_mul, mul_assoc, mul_assoc]
  rw [mul_conj, pow_two, mul_re, ofReal_re, ofReal_im, ← pow_two]
  simp

-- La norma inducida es lineal
theorem norma_inducida_lineal : @norma_lineal 𝕜 _ E _ _ (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_lineal
  intro a x
  unfold norma_inducida
  rw [lema_norma_lineal]
  rw [sqrt_mul, sqrt_sq]
  unfold modulo
  exact sqrt_nonneg (re (a * (starRingEnd 𝕜) a))
  exact sq_nonneg (modulo a)


-- Desigualdad de Cauchy-Schwarz

lemma linearidad_menos (a b c : E) : inner (a - b) c = @inner 𝕜 E _ a c - inner b c := by
  have h (b c : E) : @inner 𝕜 E _ (-b) c = - @inner 𝕜 E _ b c := by
    rw [← @neg_one_smul 𝕜 E _ _ _ b, mult_por_esc]
    simp
  rw[sub_eq_add_neg a b, linearidad, h, ← sub_eq_add_neg]

lemma lema_dcs (a b : 𝕜) (f g : E) : @inner 𝕜 E _ (a • f - b • g) (a • f - b • g) =
  a * conj a * inner f f - conj a * b * inner f g - a * conj b * inner g f + b * conj b * inner g g := by
  sorry

variable (a : E)

theorem des_cauchy_schwartz (f g : E) : modulo (@inner 𝕜 E _ f g) ^ 2 ≤ re ((@inner 𝕜 E _ f f) * (@inner 𝕜 E _ g g)) := by
  have h1 : ∀ a b : 𝕜, re (@inner 𝕜 E _ (a • f - b • g) (a • f - b • g)) ≥ 0 ∧
  im (@inner 𝕜 E _ (a • f - b • g) (a • f - b • g)) = 0 := by
    intro a b
    exact prod_esc_sim_pos
  specialize h1 (inner f g) (inner f f)
  obtain ⟨h2, _⟩ := h1
  let a : 𝕜 := inner f g
  let b : 𝕜 := inner f f
  rw[lema_dcs, @conj_symm 𝕜 E _ _ _ g f] at h2

  sorry


-- La norma inducida cumple la desigualdad triangular
theorem norma_inducida_des_triang : @norma_des_triang 𝕜 _ E _ _ (@norma_inducida 𝕜 E _ _ _) := by
  unfold norma_des_triang
  intro a b
  unfold norma_inducida
  sorry

end normaprodesc
