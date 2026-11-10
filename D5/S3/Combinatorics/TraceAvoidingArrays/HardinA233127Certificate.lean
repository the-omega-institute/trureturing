/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Exact single-row transition certificate for the square-strip recurrence. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only.
Declaration names use the D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip namespace.
Cross-module consumers retain that namespace.
class_fibres: proof_shape=bind-only; consumers=class_fibres_normalized
class_fibres_normalized: proof_shape=bind-only; consumers=completed_010101 (and every other completed/unseen boundary proof)
completed_010101: proof_shape=bind-only; consumers=row_counts
completed_010102: proof_shape=bind-only; consumers=row_counts
completed_010120: proof_shape=bind-only; consumers=row_counts
completed_010121: proof_shape=bind-only; consumers=row_counts
completed_010201: proof_shape=bind-only; consumers=row_counts
completed_010202: proof_shape=bind-only; consumers=row_counts
completed_010210: proof_shape=bind-only; consumers=row_counts
completed_010212: proof_shape=bind-only; consumers=row_counts
completed_012010: proof_shape=bind-only; consumers=row_counts
completed_012012: proof_shape=bind-only; consumers=row_counts
completed_012020: proof_shape=bind-only; consumers=row_counts
completed_012021: proof_shape=bind-only; consumers=row_counts
completed_012101: proof_shape=bind-only; consumers=row_counts
completed_012102: proof_shape=bind-only; consumers=row_counts
completed_012120: proof_shape=bind-only; consumers=row_counts
completed_012121: proof_shape=bind-only; consumers=row_counts
completed_020101: proof_shape=bind-only; consumers=row_counts
completed_020102: proof_shape=bind-only; consumers=row_counts
completed_020120: proof_shape=bind-only; consumers=row_counts
completed_020121: proof_shape=bind-only; consumers=row_counts
completed_020201: proof_shape=bind-only; consumers=row_counts
completed_020202: proof_shape=bind-only; consumers=row_counts
completed_020210: proof_shape=bind-only; consumers=row_counts
completed_020212: proof_shape=bind-only; consumers=row_counts
completed_021010: proof_shape=bind-only; consumers=row_counts
completed_021012: proof_shape=bind-only; consumers=row_counts
completed_021020: proof_shape=bind-only; consumers=row_counts
completed_021021: proof_shape=bind-only; consumers=row_counts
completed_021201: proof_shape=bind-only; consumers=row_counts
completed_021202: proof_shape=bind-only; consumers=row_counts
completed_021210: proof_shape=bind-only; consumers=row_counts
completed_021212: proof_shape=bind-only; consumers=row_counts
completed_101010: proof_shape=bind-only; consumers=row_counts
completed_101012: proof_shape=bind-only; consumers=row_counts
completed_101020: proof_shape=bind-only; consumers=row_counts
completed_101021: proof_shape=bind-only; consumers=row_counts
completed_101201: proof_shape=bind-only; consumers=row_counts
completed_101202: proof_shape=bind-only; consumers=row_counts
completed_101210: proof_shape=bind-only; consumers=row_counts
completed_101212: proof_shape=bind-only; consumers=row_counts
completed_102010: proof_shape=bind-only; consumers=row_counts
completed_102012: proof_shape=bind-only; consumers=row_counts
completed_102020: proof_shape=bind-only; consumers=row_counts
completed_102021: proof_shape=bind-only; consumers=row_counts
completed_102101: proof_shape=bind-only; consumers=row_counts
completed_102102: proof_shape=bind-only; consumers=row_counts
completed_102120: proof_shape=bind-only; consumers=row_counts
completed_102121: proof_shape=bind-only; consumers=row_counts
completed_120101: proof_shape=bind-only; consumers=row_counts
completed_120102: proof_shape=bind-only; consumers=row_counts
completed_120120: proof_shape=bind-only; consumers=row_counts
completed_120121: proof_shape=bind-only; consumers=row_counts
completed_120201: proof_shape=bind-only; consumers=row_counts
completed_120202: proof_shape=bind-only; consumers=row_counts
completed_120210: proof_shape=bind-only; consumers=row_counts
completed_120212: proof_shape=bind-only; consumers=row_counts
completed_121010: proof_shape=bind-only; consumers=row_counts
completed_121012: proof_shape=bind-only; consumers=row_counts
completed_121020: proof_shape=bind-only; consumers=row_counts
completed_121021: proof_shape=bind-only; consumers=row_counts
completed_121201: proof_shape=bind-only; consumers=row_counts
completed_121202: proof_shape=bind-only; consumers=row_counts
completed_121210: proof_shape=bind-only; consumers=row_counts
completed_121212: proof_shape=bind-only; consumers=row_counts
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
unseen_010101: proof_shape=bind-only; consumers=row_counts
unseen_101010: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
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

private theorem class_fibres_normalized (s : Seen) (p : Boundary) (k : Fin 11) :
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

private theorem unseen_010101 : ∀ k : Fin 11,
    classCount (true, false) ![0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, false) ![0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

private theorem unseen_101010 : ∀ k : Fin 11,
    classCount (true, false) ![1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, false) ![1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized]
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
      | exact unseen_010101 k
      | exact unseen_101010 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
