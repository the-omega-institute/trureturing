/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.finite_certificate
   digest: Four-row one-sided horizontal and antidiagonal pair transfer for A233259. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
escape_witness: none
recurrence: proof_shape=bind-only; consumers=HardinA233259Strip.finite_certificate, HardinA233259Strip.result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferInitial
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCount
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA233259PairTransferCore
theorem recurrence (n : ℕ) : (L (n+9) : ℤ) + 6 =
    10 * ((L (n+8) : ℤ) + 6) - 24 * ((L (n+7) : ℤ) + 6) +
      21 * ((L (n+6) : ℤ) + 6) - 6 * ((L (n+5) : ℤ) + 6) :=
  HardinA233259PairTransferRecurrence.recurrence n

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransfer
