-- ⟨ACϟDC⟩≤‖AC‖‖DC‖

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Normed.Group.Lemmas
import Mathlib.Analysis.NormedSpace.AddTorsor
import Mathlib.Analysis.NormedSpace.AffineIsometry
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.NormedSpace.RieszLemma
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.Matrix

universe u v w x

namespace uwu

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace 𝕜]

def es_limite (f: ℕ → ℝ) (t : ℝ) : Prop :=
∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ n, N ≤ n → (f n - t) ≤ ε

theorem teorema_uno {c : ℝ} (h1 : c > 0) (h2 : ∃ x : 𝕜, c > ‖x‖₊) :
(∃xn : ℕ → 𝕜, es_limite (norm ∘ xn) 0) :=
by sorry

end uwu
