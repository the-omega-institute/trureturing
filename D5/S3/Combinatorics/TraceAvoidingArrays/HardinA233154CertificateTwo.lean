/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateTwo
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.finite_certificate
   digest: The seven-column quotient rows with first code digit 2. -/

/-
admission_basis: open-problem-resolution (#29204; Proved)
escape_witness: none
row_counts: proof_shape=bind-only; consumers=HardinA233154Column.row_counts_code
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import Mathlib.Tactic

/-! Each certificate checks one disjoint block of row codes. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateTwo
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
theorem row_counts : ∀ a : Fin 729,
    rowLegal (decode 7 (⟨3*a.val + 2, by omega⟩ : Fin 2187)) → ∀ s : Fin 16,
    classCount (decode 7 (⟨3*a.val + 2, by omega⟩ : Fin 2187)) s =
      quotient (classify (decode 7 (⟨3*a.val + 2, by omega⟩ : Fin 2187))) s := by
  intro ⟨a, ha⟩
  interval_cases a <;> decide +kernel +revert

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateTwo
