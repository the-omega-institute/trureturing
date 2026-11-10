/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneB
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneB
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
Direct frozen dependencies (declaration GIDs and statement_ids):
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow
statement_id: sha256:e97b1a06b78d944d101465bdc94301416cfe964a1e9cbf900093e9cd04d04132
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowProper
statement_id: sha256:3008fde3ace25a7a7b6733df6dfc91bda36cb584aea7e431b1c29d583dc1893d
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper
statement_id: sha256:be16a774dbabce7949eb6e2bfc0026252c129abfda8a7377875535297a177b53
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.full_row
statement_id: sha256:f81e65c6e42bf750ca73737a7ace4b7b696a7b7a57684908ba1ce134acfcf88c
completed_1020101: proof_shape=bind-only; consumers=row_counts_10
completed_1020102: proof_shape=bind-only; consumers=row_counts_10
completed_1020120: proof_shape=bind-only; consumers=row_counts_10
completed_1020121: proof_shape=bind-only; consumers=row_counts_10
completed_1020201: proof_shape=bind-only; consumers=row_counts_10
completed_1020202: proof_shape=bind-only; consumers=row_counts_10
completed_1020210: proof_shape=bind-only; consumers=row_counts_10
completed_1020212: proof_shape=bind-only; consumers=row_counts_10
completed_1021010: proof_shape=bind-only; consumers=row_counts_10
completed_1021012: proof_shape=bind-only; consumers=row_counts_10
completed_1021020: proof_shape=bind-only; consumers=row_counts_10
completed_1021021: proof_shape=bind-only; consumers=row_counts_10
completed_1021201: proof_shape=bind-only; consumers=row_counts_10
completed_1021202: proof_shape=bind-only; consumers=row_counts_10
completed_1021210: proof_shape=bind-only; consumers=row_counts_10
completed_1021212: proof_shape=bind-only; consumers=row_counts_10
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open private class_fibres_normalized from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
open HardinA233255ShapeSymmetry (full_row)

private theorem completed_1020101 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020102 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020120 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020121 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020201 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020202 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020210 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1020212 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021010 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021012 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021020 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021021 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021201 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021202 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021210 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1021212 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
