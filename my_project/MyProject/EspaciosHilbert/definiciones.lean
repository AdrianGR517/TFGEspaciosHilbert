import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.IsROrC.Basic

noncomputable section

universe u v

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 :Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E]

-- Definimos la clase de producto escalar como en Mathlib
class Inner (𝕜 : Type*) (E : Type*) where
  inner : E → E → 𝕜

export Inner (inner)

-- Definimos la clase de espacios prehilbertianos como en Mathlib
class InnerProductSpace (𝕜 : Type*) (E : Type*) [IsROrC 𝕜] [AddCommGroup E] extends
  Module 𝕜 E, Inner 𝕜 E where

  prod_esc_sim_pos : re (inner x x) ≥ 0 ∧ im (inner x x) = 0
  prod_esc_cero_1 : inner x x = 0 → x = 0
  prod_esc_cero_2 : inner 0 0 = 0
  conj_symm : ∀ x y, inner x y = conj (inner y x)
  mult_por_esc : ∀ x y r, inner (r • x) y = r * inner x y
  linearidad : ∀ x y z, inner (x + y) z = inner x z + inner y z

-- ‖x‖ ≥ 0
def norma_pos (E : Type v) (norma : E → ℝ): Prop :=
  ∀ x : E, norma x ≥ 0

-- ‖x‖ = 0 ↔ x = 0
def norma_cero (E : Type v) [OfNat E 0] (norma : E → ℝ) : Prop :=
  ∀ x : E, norma (x) = 0 ↔ x = 0

-- ‖a • x‖ = |a| * ‖x‖
def modulo (a : 𝕜) : ℝ :=
  sqrt (re (a * (conj a)))

def norma_lineal (E : Type*) [AddCommGroup E] [Module 𝕜 E] (norma : E → ℝ) : Prop :=
  ∀ a : 𝕜, ∀ x : E, norma (a • x) = (modulo a) * (norma x)

-- ‖a + b‖ ≤ ‖a‖ + ‖b‖
def norma_des_triang (E : Type*) [AddCommGroup E] [Module 𝕜 E] (norma : E → ℝ) : Prop :=
  ∀ a b : E, norma (a + b) ≤ norma (a) + norma (b)
