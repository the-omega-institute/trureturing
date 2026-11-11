/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Exact square-strip scanner transitions by the first boundary label. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only.
Declaration names use the D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip namespace.
completed_101010: proof_shape=bind-only; consumers=row_counts_one
completed_101012: proof_shape=bind-only; consumers=row_counts_one
completed_101020: proof_shape=bind-only; consumers=row_counts_one
completed_101021: proof_shape=bind-only; consumers=row_counts_one
completed_101201: proof_shape=bind-only; consumers=row_counts_one
completed_101202: proof_shape=bind-only; consumers=row_counts_one
completed_101210: proof_shape=bind-only; consumers=row_counts_one
completed_101212: proof_shape=bind-only; consumers=row_counts_one
completed_102010: proof_shape=bind-only; consumers=row_counts_one
completed_102012: proof_shape=bind-only; consumers=row_counts_one
completed_102020: proof_shape=bind-only; consumers=row_counts_one
completed_102021: proof_shape=bind-only; consumers=row_counts_one
completed_102101: proof_shape=bind-only; consumers=row_counts_one
completed_102102: proof_shape=bind-only; consumers=row_counts_one
completed_102120: proof_shape=bind-only; consumers=row_counts_one
completed_102121: proof_shape=bind-only; consumers=row_counts_one
completed_120101: proof_shape=bind-only; consumers=row_counts_one
completed_120102: proof_shape=bind-only; consumers=row_counts_one
completed_120120: proof_shape=bind-only; consumers=row_counts_one
completed_120121: proof_shape=bind-only; consumers=row_counts_one
completed_120201: proof_shape=bind-only; consumers=row_counts_one
completed_120202: proof_shape=bind-only; consumers=row_counts_one
completed_120210: proof_shape=bind-only; consumers=row_counts_one
completed_120212: proof_shape=bind-only; consumers=row_counts_one
completed_121010: proof_shape=bind-only; consumers=row_counts_one
completed_121012: proof_shape=bind-only; consumers=row_counts_one
completed_121020: proof_shape=bind-only; consumers=row_counts_one
completed_121021: proof_shape=bind-only; consumers=row_counts_one
completed_121201: proof_shape=bind-only; consumers=row_counts_one
completed_121202: proof_shape=bind-only; consumers=row_counts_one
completed_121210: proof_shape=bind-only; consumers=row_counts_one
completed_121212: proof_shape=bind-only; consumers=row_counts_one
unseen_101010: proof_shape=bind-only; consumers=row_counts_one
row_counts_one: proof_shape=bind-only; consumers=row_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233255PairTransfer (Boundary)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)

attribute [local instance 2000] Pi.instFintype
open HardinA233255ShapeSymmetry (full_row)

private theorem completed_101010 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101012 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101020 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101021 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101201 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101202 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101210 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_101212 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102010 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102012 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102020 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102021 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102101 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102102 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102120 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_102121 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120101 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120102 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120120 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120121 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120201 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120202 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120210 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_120212 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121010 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121012 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121020 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121021 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121201 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121202 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121210 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_121212 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem unseen_101010 : ∀ k : Fin 11,
    classCount (true, false) ![1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, false) ![1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 2000000 in
theorem row_counts_one : ∀ s p, Valid s p → p 0 = 1 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 hp hzero k
  change p0 = (1 : Fin 3) at hzero
  subst p0
  cases b1
  · cases hp.1
  · cases b2 <;> fin_cases p1 <;> simp [Valid, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals first
      | exact completed_101010 k
      | exact completed_101012 k
      | exact completed_101020 k
      | exact completed_101021 k
      | exact completed_101201 k
      | exact completed_101202 k
      | exact completed_101210 k
      | exact completed_101212 k
      | exact completed_102010 k
      | exact completed_102012 k
      | exact completed_102020 k
      | exact completed_102021 k
      | exact completed_102101 k
      | exact completed_102102 k
      | exact completed_102120 k
      | exact completed_102121 k
      | exact completed_120101 k
      | exact completed_120102 k
      | exact completed_120120 k
      | exact completed_120121 k
      | exact completed_120201 k
      | exact completed_120202 k
      | exact completed_120210 k
      | exact completed_120212 k
      | exact completed_121010 k
      | exact completed_121012 k
      | exact completed_121020 k
      | exact completed_121021 k
      | exact completed_121201 k
      | exact completed_121202 k
      | exact completed_121210 k
      | exact completed_121212 k
      | exact unseen_101010 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
