/- GID: D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every identifying adaptive binary protocol has logarithmic fiber-diversity depth. -/

import D5.S3.ConceptDynamics.Coding.BinaryRepairCost

/- Library-search audit trail (2026-08-24):
   * Exact repository hits `BinaryProtocol`, `IdentifiesGiven`, and
     `worstFiberDiversity` in `FiberBinaryIdentification` supply the canonical
     adaptive protocol, identification predicate, and fiber-diversity object.
   * Exact repository hit
     `binary_repair_cost_is_log_of_minimal_labels` in `BinaryRepairCost`
     supplies the least feasible fixed-width binary label count.
   * Searches for `BinaryProtocol`, `IdentifiesGiven`, `clog`, and adaptive
     depth bounds in D5 found no theorem giving this general lower bound;
     `AdaptiveResidueIdentification` is a concrete four-state construction.
   * Exact pinned-Lean hit `BitVec.eq_of_getElem_eq` reconstructs a transcript
     from equality of all its bits. Exact pinned-Mathlib hits `Nat.clog_le_iff_le_pow`,
     `Nat.clog_le_of_le_pow`, and `Nat.le_pow_clog` occur in the imported
     fixed-label theorem. `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.Coding.BinaryRepairCost

/-- If a depth-`depth` adaptive binary protocol identifies the target inside
every fiber of the already-known concept, then its depth is at least the
ceiling binary logarithm of the greatest target diversity of such a fiber. -/
theorem adaptive_binary_protocol_depth_lower_bound
    {X C Target : Type*} [Fintype X] [Fintype C]
    (current : Concept X C) (target : Concept X Target)
    {depth : Nat} (protocol : BinaryProtocol X depth)
    (identifies : IdentifiesGiven current target protocol) :
    Nat.clog 2 (worstFiberDiversity current target) <= depth := by
  have feasible : BinaryRepairFeasible current target depth := by
    refine ⟨fun x round => (protocol.transcript x).getLsb round, ?_⟩
    intro x y sameCurrent sameLabel
    apply identifies x y sameCurrent
    apply BitVec.eq_of_getElem_eq
    intro bit inRange
    change (protocol.transcript x).getLsb ⟨bit, inRange⟩ =
      (protocol.transcript y).getLsb ⟨bit, inRange⟩
    exact congrFun sameLabel ⟨bit, inRange⟩
  exact (binary_repair_cost_is_log_of_minimal_labels current target).2.2 feasible

#print axioms adaptive_binary_protocol_depth_lower_bound

end D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound
