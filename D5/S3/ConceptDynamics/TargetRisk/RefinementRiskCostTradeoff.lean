/- GID: D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement shrinks target risk while increasing attained-coordinate cost. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-21):
   * Searches of D5 and the active frozen ledger for target risk, refinement
     cost, and their opposite monotonicities found no exact theorem or
     canonical risk/cost declarations.
   * Exact repository hit `ConceptJoinUniversal.Refines` is the family's
     canonical factor-map refinement relation and is applied directly.
   * Pinned Mathlib exact hits `Set.range_comp` and `Set.encard_image_le` are
     applied directly to the attained-coordinate cost conjunct.
   * The existing policy-capability theorem is adjacent but concerns ranges of
     implementable policies, not kernel defects, target families, or cost.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A source readout is defective for a target on a pair when it identifies
the two states while the target distinguishes them. -/
def defectRelation
    {X C Target : Type*} (readout : Concept X C)
    (target : Concept X Target) : Set (X × X) :=
  {pair | readout pair.1 = readout pair.2 ∧
    target pair.1 ≠ target pair.2}

/-- Target risk filters a supplied target family for targets with a nonempty
source-readout defect relation. -/
def targetRisk
    {X C Target : Type*} (readout : Concept X C)
    (targets : Set (Concept X Target)) : Set (Concept X Target) :=
  {target | target ∈ targets ∧ (defectRelation readout target).Nonempty}

/-- Refinement cost is the extended cardinality of the concept coordinates
actually attained by the readout. -/
noncomputable def refinementCost
    {X C : Type*} (readout : Concept X C) : ℕ∞ :=
  (Set.range readout).encard

/-- A finer readout has no more risky targets and no lower attained-coordinate
cost. These opposite monotonicities expose the compression-benefit versus
future-target-risk tradeoff. -/
theorem refinement_reduces_target_risk_and_raises_cost
    {X C D Target : Type*} (q_C : Concept X C) (q_D : Concept X D)
    (targets : Set (Concept X Target)) (refinement : Refines q_C q_D) :
    targetRisk q_D targets ⊆ targetRisk q_C targets ∧
      refinementCost q_C ≤ refinementCost q_D := by
  rcases refinement with ⟨factor, hfactor⟩
  constructor
  · intro target atRisk
    rcases atRisk with
      ⟨targetInFamily, ⟨pair, sameFineCoordinate, differentTarget⟩⟩
    refine ⟨targetInFamily, ⟨pair, ?_, differentTarget⟩⟩
    rw [hfactor]
    exact congrArg factor sameFineCoordinate
  · unfold refinementCost
    calc
      (Set.range q_C).encard = (Set.range (factor ∘ q_D)).encard :=
        congrArg (fun readout => (Set.range readout).encard) hfactor
      _ = (factor '' Set.range q_D).encard :=
        congrArg Set.encard (Set.range_comp factor q_D)
      _ ≤ (Set.range q_D).encard := Set.encard_image_le factor (Set.range q_D)

/-- Constant and identity readouts realize a proper coarse-to-fine
refinement. -/
example :
    Refines (fun _ : Bool => ()) (id : Concept Bool Bool) :=
  ⟨fun _ => (), rfl⟩

/-- For the identity target, the constant readout is risky while the identity
readout is not; risk inclusion can therefore fail without refinement in the
stated direction. -/
example :
    let coarse : Concept Bool Unit := fun _ => ()
    let fine : Concept Bool Bool := id
    let targets : Set (Concept Bool Bool) := {id}
    (id : Concept Bool Bool) ∈ targetRisk coarse targets ∧
      (id : Concept Bool Bool) ∉ targetRisk fine targets := by
  dsimp
  constructor
  · exact ⟨Set.mem_singleton _, ⟨(false, true), rfl, Bool.false_ne_true⟩⟩
  · rintro ⟨_, ⟨⟨left, right⟩, sameCoordinate, differentTarget⟩⟩
    exact differentTarget sameCoordinate

/-- Cost monotonicity can also fail when the refinement direction is
reversed. -/
example :
    Not (refinementCost (id : Concept Bool Bool) ≤
      refinementCost (fun _ : Bool => ())) := by
  simp only [refinementCost, Set.range_id, Set.range_const,
    Set.encard_singleton]
  rw [show (Set.univ : Set Bool) = {false, true} by
    ext value
    cases value <;> simp]
  rw [Set.encard_pair Bool.false_ne_true]
  decide

#print axioms refinement_reduces_target_risk_and_raises_cost

end D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
