/- GID: D5/S3/ConceptDynamics/RefinementFactorization/IndexedTargetDefectMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/IndexedTargetDefectMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Enlarging an indexed readout budget shrinks its target-defect relation. -/

import D5.S3.ConceptDynamics.RefinementFactorization.IndexedReadoutMonotonicity
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-24):
   * Cross-lane searches found the exact canonical primitives
     `JointFaithfulnessLeibnizCriterion.jointReadout` and
     `RefinementRiskCostTradeoff.defectRelation`; both are imported rather
     than redeclared.
   * Exact repository hit `indexed_readout_monotonicity` proves equality-kernel
     inclusion for the same finite-index readouts and is applied directly.
   * The leased atom id has no current-tree digestion record. The existing
     indexed theorem belongs to another atom and does not itself publicly state
     target-defect inclusion.
   * No additional Mathlib lemma is needed after the exact family theorem hit.
     `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.IndexedTargetDefectMonotonicity

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.RefinementFactorization.IndexedReadoutMonotonicity
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

universe u v w z

/-- Target defects of the joint readout are antitone in the finite observation
budget. Both readouts are the canonical restrictions of one indexed observation
family. -/
theorem larger_observation_budget_shrinks_target_defect
    {I : Type u} {X : Type v} {O : I -> Type w} {Target : Type z}
    (q : forall i, X -> O i) (target : X -> Target)
    {J K : Finset I} (hJK : J ⊆ K) :
    defectRelation (jointReadout (fun k : K => q k.1)) target ⊆
      defectRelation (jointReadout (fun j : J => q j.1)) target := by
  intro pair defect
  refine ⟨?_, defect.2⟩
  exact (indexed_readout_monotonicity q hJK).2 defect.1

#print axioms larger_observation_budget_shrinks_target_defect

end D5.S3.ConceptDynamics.RefinementFactorization.IndexedTargetDefectMonotonicity
