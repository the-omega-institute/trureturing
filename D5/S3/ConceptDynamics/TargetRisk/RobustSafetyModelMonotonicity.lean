/- GID: D5/S3/ConceptDynamics/TargetRisk/RobustSafetyModelMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TargetRisk/RobustSafetyModelMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Enlarging the audited model family can only shrink the robust safe-action set. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Order

/- Library-search audit trail (2026-08-25):
   * Repository searches for robust safety, model uncertainty, worst-case risk,
     risk thresholds, and the atom fingerprint found no exact theorem or canonical
     model-indexed safe-set definition.
   * The adjacent `TargetRisk` family concerns defects of concept readouts rather
     than disaster risk indexed by an admissible model family.
   * Pinned Mathlib exact hit `Set.antitone_bforall` states that bounded universal
     quantification is antitone in the bounding set and is applied directly below.
   * `loogle` and `leansearch` are unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TargetRisk.RobustSafetyModelMonotonicity

/-- Actions are constructed as robustly safe when every admitted model assigns
risk at most the supplied threshold. Enlarging the admitted model family can
therefore only remove safe actions. -/
theorem model_uncertainty_expansion_shrinks_safe_set
    {Model Action : Type*} (risk : Model -> Action -> Real) (threshold : Real)
    {models expandedModels : Set Model} (expansion : models ⊆ expandedModels) :
    {action | forall model, model ∈ expandedModels -> risk model action <= threshold} ⊆
      {action | forall model, model ∈ models -> risk model action <= threshold} := by
  intro action safeForExpandedModels
  exact Set.antitone_bforall expansion safeForExpandedModels

#print axioms model_uncertainty_expansion_shrinks_safe_set

end D5.S3.ConceptDynamics.TargetRisk.RobustSafetyModelMonotonicity
