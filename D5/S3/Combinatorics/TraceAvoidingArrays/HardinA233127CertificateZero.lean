/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Exact square-strip scanner transitions by the first boundary label. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only.
Declaration names use the D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip namespace.
class_fibres: proof_shape=bind-only; consumers=class_fibres_normalized
class_fibres_normalized: proof_shape=bind-only; consumers=completed_010101; used by all completed/unseen boundary proofs
completed_010101: proof_shape=bind-only; consumers=row_counts_zero
completed_010102: proof_shape=bind-only; consumers=row_counts_zero
completed_010120: proof_shape=bind-only; consumers=row_counts_zero
completed_010121: proof_shape=bind-only; consumers=row_counts_zero
completed_010201: proof_shape=bind-only; consumers=row_counts_zero
completed_010202: proof_shape=bind-only; consumers=row_counts_zero
completed_010210: proof_shape=bind-only; consumers=row_counts_zero
completed_010212: proof_shape=bind-only; consumers=row_counts_zero
completed_012010: proof_shape=bind-only; consumers=row_counts_zero
completed_012012: proof_shape=bind-only; consumers=row_counts_zero
completed_012020: proof_shape=bind-only; consumers=row_counts_zero
completed_012021: proof_shape=bind-only; consumers=row_counts_zero
completed_012101: proof_shape=bind-only; consumers=row_counts_zero
completed_012102: proof_shape=bind-only; consumers=row_counts_zero
completed_012120: proof_shape=bind-only; consumers=row_counts_zero
completed_012121: proof_shape=bind-only; consumers=row_counts_zero
completed_020101: proof_shape=bind-only; consumers=row_counts_zero
completed_020102: proof_shape=bind-only; consumers=row_counts_zero
completed_020120: proof_shape=bind-only; consumers=row_counts_zero
completed_020121: proof_shape=bind-only; consumers=row_counts_zero
completed_020201: proof_shape=bind-only; consumers=row_counts_zero
completed_020202: proof_shape=bind-only; consumers=row_counts_zero
completed_020210: proof_shape=bind-only; consumers=row_counts_zero
completed_020212: proof_shape=bind-only; consumers=row_counts_zero
completed_021010: proof_shape=bind-only; consumers=row_counts_zero
completed_021012: proof_shape=bind-only; consumers=row_counts_zero
completed_021020: proof_shape=bind-only; consumers=row_counts_zero
completed_021021: proof_shape=bind-only; consumers=row_counts_zero
completed_021201: proof_shape=bind-only; consumers=row_counts_zero
completed_021202: proof_shape=bind-only; consumers=row_counts_zero
completed_021210: proof_shape=bind-only; consumers=row_counts_zero
completed_021212: proof_shape=bind-only; consumers=row_counts_zero
unseen_010101: proof_shape=bind-only; consumers=row_counts_zero
row_counts_zero: proof_shape=bind-only; consumers=row_counts
-/

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

private theorem class_fibres (s : Seen) (p : Boundary) (k : Fin 11) :
    classCount s p k = ∑ q : Boundary,
      rowWeight s q * if (∀ j : Fin 5, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 6 s (fun t q =>
    if (∀ j : Fin 5, q j.castSucc ≠ q j.succ) ∧
      (∀ j, p j ≠ q j) ∧ boundaryClass t q = k then (1 : ℤ) else 0)]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  simp only [← colour_bond_iff]
  change (if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) =
    if good s c then (if rowLegal c ∧ compatible p c ∧
      boundaryClass (finish s c) (labels c) = k then 1 else 0) else 0
  by_cases hg : good s c <;> simp [hg]

theorem class_fibres_normalized (s : Seen) (p : Boundary) (k : Fin 11) :
    classCount s p k =
      ∑ q0 : Fin 3, ∑ q1 : Fin 3, ∑ q2 : Fin 3, ∑ q3 : Fin 3,
      ∑ q4 : Fin 3, ∑ q5 : Fin 3,
      rowWeight s ![q0, q1, q2, q3, q4, q5] *
      if (∀ j : Fin 5, (![q0, q1, q2, q3, q4, q5] : Boundary) j.castSucc ≠
        (![q0, q1, q2, q3, q4, q5] : Boundary) j.succ) ∧
        (∀ j : Fin 6, p j ≠ (![q0, q1, q2, q3, q4, q5] : Boundary) j) ∧
        boundaryClass (rowFinish s ![q0, q1, q2, q3, q4, q5])
          ![q0, q1, q2, q3, q4, q5] = k then 1 else 0 := by
  simp only [class_fibres]
  simp_rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 5 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin 3)).sum_comp,
    Fintype.sum_prod_type]
  simp [Fin.consEquiv, Matrix.empty_eq]

private theorem completed_010101 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010102 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010120 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010121 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010201 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010202 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010210 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_010212 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012010 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012012 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012020 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012021 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012101 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012102 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012120 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_012121 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020101 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020102 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020120 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020121 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020201 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020202 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020210 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_020212 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021010 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021012 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021020 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021021 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021201 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021202 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021210 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem completed_021212 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 6 _).1, (full_row 6 _).2]
  decide +kernel

private theorem unseen_010101 : ∀ k : Fin 11,
    classCount (true, false) ![0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, false) ![0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 2000000 in
theorem row_counts_zero : ∀ s p, Valid s p → p 0 = 0 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 hp hzero k
  change p0 = (0 : Fin 3) at hzero
  subst p0
  cases b1
  · cases hp.1
  · cases b2 <;> fin_cases p1 <;> simp [Valid, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals first
      | exact completed_010101 k
      | exact completed_010102 k
      | exact completed_010120 k
      | exact completed_010121 k
      | exact completed_010201 k
      | exact completed_010202 k
      | exact completed_010210 k
      | exact completed_010212 k
      | exact completed_012010 k
      | exact completed_012012 k
      | exact completed_012020 k
      | exact completed_012021 k
      | exact completed_012101 k
      | exact completed_012102 k
      | exact completed_012120 k
      | exact completed_012121 k
      | exact completed_020101 k
      | exact completed_020102 k
      | exact completed_020120 k
      | exact completed_020121 k
      | exact completed_020201 k
      | exact completed_020202 k
      | exact completed_020210 k
      | exact completed_020212 k
      | exact completed_021010 k
      | exact completed_021012 k
      | exact completed_021020 k
      | exact completed_021021 k
      | exact completed_021201 k
      | exact completed_021202 k
      | exact completed_021210 k
      | exact completed_021212 k
      | exact unseen_010101 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
