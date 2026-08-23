/- GID: D5/S3/Entropy/Submodularity/PredictiveMemoryMonotonicity
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/PredictiveMemoryMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predictive memory decreases when a deterministic readout is refined. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.Entropy.Submodularity.RefinementInformationDecomposition

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `ConceptJoinUniversal.Refines` supplies the canonical
     factorization order on deterministic readouts and is imported directly.
   * Exact repository hits `predictiveMemory` and
     `deterministic_refinement_information_decomposition` supply the canonical
     quantity and the stronger exact nonnegative difference theorem; the latter
     is applied directly.
   * Searches of repository and pinned-Mathlib declarations for predictive-memory
     monotonicity found no theorem already exposing this order inequality. -/

namespace D5.S3.Entropy.Submodularity.PredictiveMemoryMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.Entropy.Submodularity.RefinementInformationDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Refining a deterministic readout can only reduce the predictive memory left
beyond that readout. -/
theorem predictive_memory_monotone_under_refinement
    {P F Fine Coarse : Type*}
    [Fintype P] [Fintype F] [Fintype Fine] [Fintype Coarse]
    (p : P × F -> Real)
    (hp : (forall z, 0 <= p z) /\ ∑ z, p z = 1)
    (fine : Concept P Fine) (coarse : Concept P Coarse)
    (refines : Refines coarse fine) :
    predictiveMemory p fine <= predictiveMemory p coarse := by
  rcases refines with ⟨forget, hcoarse⟩
  rw [hcoarse]
  have decomposition :=
    deterministic_refinement_information_decomposition p hp fine forget
  linarith [decomposition.1, decomposition.2]

-- A fair Boolean law and the constant quotient witness all public hypotheses.
example :
    let p : Bool × Bool -> Real := fun z => if z.1 = z.2 then 1 / 2 else 0
    predictiveMemory p (id : Concept Bool Bool) <=
      predictiveMemory p (fun _ : Bool => ()) := by
  dsimp only
  apply predictive_memory_monotone_under_refinement
    (p := fun z : Bool × Bool => if z.1 = z.2 then 1 / 2 else 0)
    (fine := id) (coarse := fun _ => ())
  · constructor
    · intro z
      split_ifs <;> norm_num
    · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
  · exact ⟨fun _ => (), rfl⟩

#print axioms predictive_memory_monotone_under_refinement

end D5.S3.Entropy.Submodularity.PredictiveMemoryMonotonicity
