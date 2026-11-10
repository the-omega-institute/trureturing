/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneE
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneE
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Exact single-row boundary transition identities. -/

/-
admission_basis: open-problem-resolution (#28672; Proved)
escape_witness: none; all-height class reduction is semiconjugacy iteration.
After normalizing finite one-step premises, v_eq_w is an instance of
Function.Semiconj.iterate_right. It and its downstream chain are bind-only.
Declaration namespace: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
DIRECT_FROZEN_DEPENDENCIES
DECLARATION_CONSUMERS
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open private class_fibres_normalized from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
open HardinA233255ShapeSymmetry (full_row)

private theorem unseen_1010101 : ∀ k : Fin 21,
    classCount (true, false) ![1, 0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, false) ![1, 0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
