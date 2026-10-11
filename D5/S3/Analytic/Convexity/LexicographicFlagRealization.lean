/- GID: D5/S3/Analytic/Convexity/LexicographicFlagRealization
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/LexicographicFlagRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite feasibility admits an orthonormal lexicographic list bounded by input rank. -/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

noncomputable section

open scoped InnerProductSpace
open Module Set

namespace D5.S3.Analytic.Convexity.LexicographicFlagRealization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {I : Type*}

/-- Every finite set of rows has one strictly positive input. -/
def FiniteFeasible (a : I → V) : Prop :=
  ∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ⟪a i, x⟫_ℝ

/-- Every row has a positive first nonzero entry in the same ordered list. -/
def LexWitness (a : I → V) {r : ℕ} (v : Fin r → V) : Prop :=
  ∀ i, ∃ k, 0 < ⟪a i, v k⟫_ℝ ∧ ∀ j < k, ⟪a i, v j⟫_ℝ = 0

end D5.S3.Analytic.Convexity.LexicographicFlagRealization
