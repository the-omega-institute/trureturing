/- GID: D5/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeStateJoin
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeStateJoin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commitment memory obstructs endpoint reduction and forces the joint normative readout. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.NormativeStructure.CommitmentNormativeMemory

/- Library-search audit trail (2026-08-27):
   * The frozen `committed_permissions_do_not_factor_through_physical_state`
     theorem is the exact endpoint-only factorization obstruction.
   * The canonical `conceptJoin`, `Refines`, and `concept_join_universal`
     declarations are imported from the existing ConceptDynamics family.
   * Searches for commitment memory conjoined with a joint-readout lower bound
     found no exact repository or pinned-library theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.CommitmentNormativeStateJoin

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.NormativeStructure.CommitmentNormativeMemory

/-- Different committed permissions at one physical endpoint obstruct every
endpoint-only permission readout. Moreover, any normative state retaining both
the current physical state and the commitment ledger refines their canonical
joint readout. -/
theorem commitment_normative_state_join
    {History PhysicalState Policy : Type*}
    (endpoint : Concept History PhysicalState)
    (committedPermissions : Concept History (Set Policy))
    (first second : History)
    (samePhysicalState : endpoint first = endpoint second)
    (differentPermissions :
      committedPermissions first ≠ committedPermissions second) :
    (¬ ∃ statePermissions : PhysicalState -> Set Policy,
      committedPermissions = statePermissions ∘ endpoint) ∧
      ∀ {NormativeState : Type*}
        (normativeState : Concept History NormativeState),
        Refines endpoint normativeState ->
        Refines committedPermissions normativeState ->
        Refines (conceptJoin endpoint committedPermissions) normativeState := by
  constructor
  · exact committed_permissions_do_not_factor_through_physical_state
      endpoint committedPermissions first second samePhysicalState differentPermissions
  · intro NormativeState normativeState endpointRetained commitmentRetained
    exact (concept_join_universal endpoint committedPermissions normativeState).2.2
      endpointRetained commitmentRetained

#print axioms commitment_normative_state_join

end D5.S3.ConceptDynamics.NormativeStructure.CommitmentNormativeStateJoin
