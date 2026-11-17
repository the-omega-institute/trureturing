/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneC
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneC
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
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow
statement_id: sha256:e97b1a06b78d944d101465bdc94301416cfe964a1e9cbf900093e9cd04d04132
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row
statement_id: sha256:bfdef18389c25a4e0e0289ec0c41644aaf42d71c7a4d540ac5103952779dfd2c
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowLegal
statement_id: sha256:566fa77bfdf47796ff0524d5a78f68b96413ca55006aa1429a767aad72408b70
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal
statement_id: sha256:ad59d456a8f5b2710481be3ed4a9d79e276a0e4319f7b6918310d350fc440508
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.full_row
statement_id: sha256:f81e65c6e42bf750ca73737a7ace4b7b696a7b7a57684908ba1ce134acfcf88c
GID: D5/S3/Observer/Separation/BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
completed_1201010: proof_shape=bind-only; consumers=row_counts_12
completed_1201012: proof_shape=bind-only; consumers=row_counts_12
completed_1201020: proof_shape=bind-only; consumers=row_counts_12
completed_1201021: proof_shape=bind-only; consumers=row_counts_12
completed_1201201: proof_shape=bind-only; consumers=row_counts_12
completed_1201202: proof_shape=bind-only; consumers=row_counts_12
completed_1201210: proof_shape=bind-only; consumers=row_counts_12
completed_1201212: proof_shape=bind-only; consumers=row_counts_12
completed_1202010: proof_shape=bind-only; consumers=row_counts_12
completed_1202012: proof_shape=bind-only; consumers=row_counts_12
completed_1202020: proof_shape=bind-only; consumers=row_counts_12
completed_1202021: proof_shape=bind-only; consumers=row_counts_12
completed_1202101: proof_shape=bind-only; consumers=row_counts_12
completed_1202102: proof_shape=bind-only; consumers=row_counts_12
completed_1202120: proof_shape=bind-only; consumers=row_counts_12
completed_1202121: proof_shape=bind-only; consumers=row_counts_12
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

/-! Exact single-row boundary transition identities. -/

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open private class_fibres_normalized from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
open HardinA233255ShapeSymmetry (full_row)

private theorem completed_1201010 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201012 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201020 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201021 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201201 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201202 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201210 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1201212 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202010 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202012 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202020 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202021 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202101 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202102 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202120 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1202121 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
