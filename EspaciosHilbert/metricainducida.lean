import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.IsROrC.Basic

import EspaciosHilbert.definiciones
import EspaciosHilbert.lemas
import EspaciosHilbert.cauchyschwarz
import EspaciosHilbert.normainducida

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

variable {𝕜 :Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E]

-- 0 ≤ ρ(x,y)
def metrica_pos (E : Type*) (ρ : E → E → ℝ) : Prop :=
  ∀ x y : E, 0 ≤ ρ x y

def metrica_inducida_pos : metrica_pos E (@dist_ind 𝕜 E _ _ _) := by
  unfold metrica_pos dist_ind
  intro x y
  let h := @norma_inducida_pos 𝕜 E _ _ _ (x - y)
  unfold norma_pos at h
  exact h

-- ρ(x,y) = 0 ↔ x = y
def metrica_cero (E : Type*) (ρ : E → E → ℝ) : Prop :=
  ∀ x y : E, ρ x y = 0 ↔ x = y

def metrica_inducida_cero : metrica_cero E (@dist_ind 𝕜 E _ _ _) := by
  unfold metrica_cero dist_ind
  intro x y
  let h := @norma_inducida_cero 𝕜 E _ _ _ (x - y)
  rw[sub_eq_zero] at h
  exact h

-- ρ(x,y) = ρ(y,x)
def metrica_sim (E : Type*) (ρ : E → E → ℝ) : Prop :=
  ∀ x y : E, ρ x y = ρ y x

def metrica_inducida_sim : metrica_sim E (@dist_ind 𝕜 E _ _ _) := by
  unfold metrica_sim dist_ind
  intro x y
  let h := @norma_inducida_lineal 𝕜 E _ _ _ (-1 : 𝕜) (x - y)
  have eq1 : modulo (-(1 : 𝕜)) = (1 : ℝ) := by
    unfold modulo
    simp
  rw[@smul_sub 𝕜 E _ _ _ (-1) x y, eq1, neg_one_smul, neg_one_smul, @neg_sub_neg E,
  one_mul, eq_comm] at h
  exact h

-- ρ(x,z) ≤ ρ(x,y) + ρ(y,z)
def metrica_dt (E : Type*) (ρ : E → E → ℝ) : Prop :=
  ∀ x y z : E, ρ x z ≤ ρ x y + ρ y z

def metrica_inducida_dt : metrica_dt E (@dist_ind 𝕜 E _ _ _) := by
  unfold metrica_dt dist_ind
  intro x y z
  let h := (@norma_inducida_des_triang 𝕜 E _ _ _)
  unfold norma_inducida_des_triang norma_des_triang at h
  specialize h (x - y) (y - z)
  rw[sub_add_sub_cancel] at h
  exact h

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
