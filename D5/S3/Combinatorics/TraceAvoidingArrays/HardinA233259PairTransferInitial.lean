/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferInitial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferInitial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.finite_certificate
   digest: Four-row initial pair-class weight certificate. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
escape_witness: none
initial_weights: proof_shape=bind-only; consumers=HardinA233259PairTransferCount.count_transfer
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import Mathlib.Tactic

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferInitial
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem initial_weights : ∀ s : Fin 14,
    (∑ a : Col, ∑ b : Col,
      if compatible a b ∧ cls b = s then (1 : ℤ) else 0) = weights s := by
  decide +kernel

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferInitial
