/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Exact square-strip scanner transitions by the first boundary label. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only.
Declaration names use the D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip namespace.
completed_201010: proof_shape=bind-only; consumers=row_counts
completed_201012: proof_shape=bind-only; consumers=row_counts
completed_201020: proof_shape=bind-only; consumers=row_counts
completed_201021: proof_shape=bind-only; consumers=row_counts
completed_201201: proof_shape=bind-only; consumers=row_counts
completed_201202: proof_shape=bind-only; consumers=row_counts
completed_201210: proof_shape=bind-only; consumers=row_counts
completed_201212: proof_shape=bind-only; consumers=row_counts
completed_202010: proof_shape=bind-only; consumers=row_counts
completed_202012: proof_shape=bind-only; consumers=row_counts
completed_202020: proof_shape=bind-only; consumers=row_counts
completed_202021: proof_shape=bind-only; consumers=row_counts
completed_202101: proof_shape=bind-only; consumers=row_counts
completed_202102: proof_shape=bind-only; consumers=row_counts
completed_202120: proof_shape=bind-only; consumers=row_counts
completed_202121: proof_shape=bind-only; consumers=row_counts
completed_210101: proof_shape=bind-only; consumers=row_counts
completed_210102: proof_shape=bind-only; consumers=row_counts
completed_210120: proof_shape=bind-only; consumers=row_counts
completed_210121: proof_shape=bind-only; consumers=row_counts
completed_210201: proof_shape=bind-only; consumers=row_counts
completed_210202: proof_shape=bind-only; consumers=row_counts
completed_210210: proof_shape=bind-only; consumers=row_counts
completed_210212: proof_shape=bind-only; consumers=row_counts
completed_212010: proof_shape=bind-only; consumers=row_counts
completed_212012: proof_shape=bind-only; consumers=row_counts
completed_212020: proof_shape=bind-only; consumers=row_counts
completed_212021: proof_shape=bind-only; consumers=row_counts
completed_212101: proof_shape=bind-only; consumers=row_counts
completed_212102: proof_shape=bind-only; consumers=row_counts
completed_212120: proof_shape=bind-only; consumers=row_counts
completed_212121: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateOne
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233254TriangleStrip (Row rowLegal)
open HardinA233255PairTransfer (Boundary)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
open HardinA233255ShapeSymmetry (full_row)

private theorem completed_201010 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201012 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201020 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201021 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201201 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201202 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201210 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_201212 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202010 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202012 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202020 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202021 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202101 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202102 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202120 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_202121 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210101 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210102 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210120 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210121 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210201 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210202 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210210 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_210212 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212010 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212012 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212020 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212021 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212101 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212102 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212120 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_212121 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 2000000 in
-- Exhaust the 98 legal boundaries after rejecting the other label rows.
theorem row_counts : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 hp k
  cases b1
  · cases hp.1
  · cases b2 <;> fin_cases p0 <;> fin_cases p1 <;>
      simp [Valid, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals first
      | exact row_counts_zero _ _ hp rfl k
      | exact row_counts_one _ _ hp rfl k
      | exact completed_201010 k
      | exact completed_201012 k
      | exact completed_201020 k
      | exact completed_201021 k
      | exact completed_201201 k
      | exact completed_201202 k
      | exact completed_201210 k
      | exact completed_201212 k
      | exact completed_202010 k
      | exact completed_202012 k
      | exact completed_202020 k
      | exact completed_202021 k
      | exact completed_202101 k
      | exact completed_202102 k
      | exact completed_202120 k
      | exact completed_202121 k
      | exact completed_210101 k
      | exact completed_210102 k
      | exact completed_210120 k
      | exact completed_210121 k
      | exact completed_210201 k
      | exact completed_210202 k
      | exact completed_210210 k
      | exact completed_210212 k
      | exact completed_212010 k
      | exact completed_212012 k
      | exact completed_212020 k
      | exact completed_212021 k
      | exact completed_212101 k
      | exact completed_212102 k
      | exact completed_212120 k
      | exact completed_212121 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
