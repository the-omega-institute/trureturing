/- GID: D5/S3/ConceptDynamics/Agency/SelfConstraintMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/SelfConstraintMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Appending a ledger constraint can only shrink the consistent action set. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-27):
   * Repository searches found risk-threshold and adjudication-closure
     specializations, but no theorem on an appended record ledger and a general
     state-indexed record/action constraint.
   * Body-shape searches for universal consistency over
     `oldLedger ++ [newRecord]` found no existing D5 primitive, so both action
     sets are constructed directly in the public statement.
   * Pinned Mathlib supplies `List.mem_append_left`, which transports every old
     record into the extended ledger; no packaged theorem states the complete
     source construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.SelfConstraintMonotonicity

/-- Every action consistent with all records after one append remains
consistent with every record of the old ledger. -/
theorem appended_record_shrinks_consistent_actions
    {State Record Action : Type*}
    (consistent : State -> Record -> Action -> Prop)
    (state : State) (oldLedger : List Record) (newRecord : Record) :
    {action | forall record, record ∈ oldLedger ++ [newRecord] ->
        consistent state record action} ⊆
      {action | forall record, record ∈ oldLedger ->
        consistent state record action} := by
  intro action consistentWithExtendedLedger record inOldLedger
  exact consistentWithExtendedLedger record
    (List.mem_append_left [newRecord] inOldLedger)

#print axioms appended_record_shrinks_consistent_actions

end D5.S3.ConceptDynamics.Agency.SelfConstraintMonotonicity
