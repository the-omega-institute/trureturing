/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateZero
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateZero
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Exact single-row transitions partitioned by the first boundary label. -/

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
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip (widthLegal colour_bond_iff)
open HardinA233255PairTransfer (Row rowLegal PairRow rowProper)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
private theorem class_fibres (s : Seen) (p : PairRow) (k : Fin 21) :
    classCount s p k = ∑ q : PairRow,
      rowWeight s q * if (∀ j : Fin 6, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 7 s (fun t q =>
    if (∀ j : Fin 6, q j.castSucc ≠ q j.succ) ∧
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

private theorem class_fibres_normalized (s : Seen) (p : PairRow) (k : Fin 21) :
    classCount s p k =
      ∑ q0 : Fin 3, ∑ q1 : Fin 3, ∑ q2 : Fin 3, ∑ q3 : Fin 3,
      ∑ q4 : Fin 3, ∑ q5 : Fin 3, ∑ q6 : Fin 3,
      rowWeight s ![q0, q1, q2, q3, q4, q5, q6] *
      if rowProper ![q0, q1, q2, q3, q4, q5, q6] ∧
        (∀ j : Fin 7, p j ≠ (![q0, q1, q2, q3, q4, q5, q6] : PairRow) j) ∧
        boundaryClass (rowFinish s ![q0, q1, q2, q3, q4, q5, q6])
          ![q0, q1, q2, q3, q4, q5, q6] = k then 1 else 0 := by
  simp only [class_fibres]
  simp_rw [← (Fin.consEquiv (fun _ : Fin 7 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 6 => Fin 3)).sum_comp,
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
  simp [Fin.consEquiv, Matrix.empty_eq, rowProper]

open HardinA233255ShapeSymmetry (full_row)

private theorem completed_0101010 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101012 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101020 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101021 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101201 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101202 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101210 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0101212 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102010 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102012 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102020 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102021 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102101 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102102 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102120 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0102121 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120101 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120102 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120120 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120121 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120201 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120202 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120210 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0120212 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121010 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121012 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121020 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121021 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121201 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121202 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121210 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0121212 : ∀ k : Fin 21,
    classCount (true, true) ![0, 1, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201010 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201012 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201020 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201021 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201201 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201202 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201210 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0201212 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202010 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202012 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202020 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202021 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202101 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202102 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202120 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0202121 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210101 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210102 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210120 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210121 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210201 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210202 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210210 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0210212 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212010 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212012 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212020 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212021 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212101 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212102 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212120 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_0212121 : ∀ k : Fin 21,
    classCount (true, true) ![0, 2, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem unseen_0101010 : ∀ k : Fin 21,
    classCount (true, false) ![0, 1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, false) ![0, 1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 4000000 in
private theorem row_counts_zero : ∀ s p, Valid s p → p 0 = 0 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst k
  change p0 = (0 : Fin 3) at hfirst
  subst p0
  cases b1
  · cases hp.1
  · cases b2 <;> fin_cases p1 <;> simp [Valid, rowProper, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals fin_cases p6 <;> simp at hp
    all_goals first
      | exact completed_0101010 k
      | exact completed_0101012 k
      | exact completed_0101020 k
      | exact completed_0101021 k
      | exact completed_0101201 k
      | exact completed_0101202 k
      | exact completed_0101210 k
      | exact completed_0101212 k
      | exact completed_0102010 k
      | exact completed_0102012 k
      | exact completed_0102020 k
      | exact completed_0102021 k
      | exact completed_0102101 k
      | exact completed_0102102 k
      | exact completed_0102120 k
      | exact completed_0102121 k
      | exact completed_0120101 k
      | exact completed_0120102 k
      | exact completed_0120120 k
      | exact completed_0120121 k
      | exact completed_0120201 k
      | exact completed_0120202 k
      | exact completed_0120210 k
      | exact completed_0120212 k
      | exact completed_0121010 k
      | exact completed_0121012 k
      | exact completed_0121020 k
      | exact completed_0121021 k
      | exact completed_0121201 k
      | exact completed_0121202 k
      | exact completed_0121210 k
      | exact completed_0121212 k
      | exact completed_0201010 k
      | exact completed_0201012 k
      | exact completed_0201020 k
      | exact completed_0201021 k
      | exact completed_0201201 k
      | exact completed_0201202 k
      | exact completed_0201210 k
      | exact completed_0201212 k
      | exact completed_0202010 k
      | exact completed_0202012 k
      | exact completed_0202020 k
      | exact completed_0202021 k
      | exact completed_0202101 k
      | exact completed_0202102 k
      | exact completed_0202120 k
      | exact completed_0202121 k
      | exact completed_0210101 k
      | exact completed_0210102 k
      | exact completed_0210120 k
      | exact completed_0210121 k
      | exact completed_0210201 k
      | exact completed_0210202 k
      | exact completed_0210210 k
      | exact completed_0210212 k
      | exact completed_0212010 k
      | exact completed_0212012 k
      | exact completed_0212020 k
      | exact completed_0212021 k
      | exact completed_0212101 k
      | exact completed_0212102 k
      | exact completed_0212120 k
      | exact completed_0212121 k
      | exact unseen_0101010 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
