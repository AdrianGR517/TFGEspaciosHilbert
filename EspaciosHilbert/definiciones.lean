import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.IsROrC.Basic

noncomputable section

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 : Type*} {E : Type*} [IsROrC 𝕜] [AddCommGroup E]

-- Definimos la clase de producto escalar como en Mathlib
class Inner (𝕜 : Type*) (E : Type*) where
  inner : E → E → 𝕜

export Inner (inner)

-- Definimos la clase de espacios prehilbertianos como en Mathlib
class InnerProductSpace (𝕜 : Type*) (E : Type*) [IsROrC 𝕜] [AddCommGroup E] extends
  Module 𝕜 E, Inner 𝕜 E where

  prod_esc_ref_pos : 0 ≤ re (inner x x) ∧ im (inner x x) = 0
  prod_esc_cero_1 : inner x x = 0 → x = 0
  prod_esc_cero_2 : inner 0 0 = 0
  conj_symm : ∀ x y, inner x y = conj (inner y x)
  mult_por_esc : ∀ x y r, inner (r • x) y = r * inner x y
  linealidad : ∀ x y z, inner (x + y) z = inner x z + inner y z

-- Definimos la norma inducida por el producto escalar
def norma_inducida [InnerProductSpace 𝕜 E] (x : E) : ℝ :=
  sqrt (re (@inner 𝕜 E _ x x))

-- Métrica inducida
def dist_ind [InnerProductSpace 𝕜 E] (f g : E) : ℝ :=
  @norma_inducida 𝕜 E _ _ _ (f - g)

-- Propiedad de sucesión de Cauchy
def deCauchy {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E] (xn : ℕ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n p : ℕ, N < n → (@dist_ind 𝕜 E _ _ _ (xn n) (xn (n + p))) < ε

-- Propiedades de sucesión convergente
def convergente' {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E] (xn : ℕ → E) (x : E): Prop :=
  ∀ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N < n → (@dist_ind 𝕜 E _ _ _ (xn n) x) < ε

def convergente {E : Type*} [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E] (xn : ℕ → E) : Prop :=
  ∃ x : E, @convergente' 𝕜 E _ _ _ xn x

-- Propiedad de espacio completo
def completo (E : Type*) [IsROrC 𝕜] [AddCommGroup E] [InnerProductSpace 𝕜 E] : Prop :=
  ∀ xn : ℕ → E, @deCauchy 𝕜 E _ _ _ xn → @convergente 𝕜 E _ _ _ xn

-- Concepto de espacio de Hilbert
class HilbertSpace (𝕜 : Type*) (E : Type*) [IsROrC 𝕜] [AddCommGroup E] extends
  InnerProductSpace 𝕜 E where
  completitud : @completo 𝕜 E _ _ _

-- Definición propia de módulo
def modulo (a : 𝕜) [IsROrC 𝕜] : ℝ :=
  sqrt (re (a * (conj a)))

-- Definimos los operadores lineales acotados como una extensión de los
-- operadores lineales ya definidos en MathLib
structure IsBoundedLinearMap (𝕜 : Type*) [IsROrC 𝕜] {E : Type*} [AddCommGroup E]
  [InnerProductSpace 𝕜 E] {F : Type*} [AddCommGroup F] [InnerProductSpace 𝕜 F] (f : E → F) extends
  IsLinearMap 𝕜 f where
  bound : ∃ M : ℝ, 0 < M ∧ ∀ x : E, re (@norma_inducida 𝕜 F _ _ _ (f x)) ≤
  M * (@norma_inducida 𝕜 E _ _ _ x)
