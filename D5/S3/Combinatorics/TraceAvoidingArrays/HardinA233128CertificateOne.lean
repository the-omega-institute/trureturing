/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOne
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

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZero
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
open private class_fibres_normalized from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZero

open HardinA233255ShapeSymmetry (full_row)

private theorem completed_1010101 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010102 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010120 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010121 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010201 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010202 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010210 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1010212 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012010 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012012 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012020 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012021 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012101 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012102 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012120 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1012121 : ∀ k : Fin 21,
    classCount (true, true) ![1, 0, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

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

private theorem completed_1210101 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210102 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210120 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210121 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210201 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210202 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210210 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1210212 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212010 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212012 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212020 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212021 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212101 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212102 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212120 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_1212121 : ∀ k : Fin 21,
    classCount (true, true) ![1, 2, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem unseen_1010101 : ∀ k : Fin 21,
    classCount (true, false) ![1, 0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, false) ![1, 0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 4000000 in
private theorem row_counts_one : ∀ s p, Valid s p → p 0 = 1 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst k
  change p0 = (1 : Fin 3) at hfirst
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
      | exact completed_1010101 k
      | exact completed_1010102 k
      | exact completed_1010120 k
      | exact completed_1010121 k
      | exact completed_1010201 k
      | exact completed_1010202 k
      | exact completed_1010210 k
      | exact completed_1010212 k
      | exact completed_1012010 k
      | exact completed_1012012 k
      | exact completed_1012020 k
      | exact completed_1012021 k
      | exact completed_1012101 k
      | exact completed_1012102 k
      | exact completed_1012120 k
      | exact completed_1012121 k
      | exact completed_1020101 k
      | exact completed_1020102 k
      | exact completed_1020120 k
      | exact completed_1020121 k
      | exact completed_1020201 k
      | exact completed_1020202 k
      | exact completed_1020210 k
      | exact completed_1020212 k
      | exact completed_1021010 k
      | exact completed_1021012 k
      | exact completed_1021020 k
      | exact completed_1021021 k
      | exact completed_1021201 k
      | exact completed_1021202 k
      | exact completed_1021210 k
      | exact completed_1021212 k
      | exact completed_1201010 k
      | exact completed_1201012 k
      | exact completed_1201020 k
      | exact completed_1201021 k
      | exact completed_1201201 k
      | exact completed_1201202 k
      | exact completed_1201210 k
      | exact completed_1201212 k
      | exact completed_1202010 k
      | exact completed_1202012 k
      | exact completed_1202020 k
      | exact completed_1202021 k
      | exact completed_1202101 k
      | exact completed_1202102 k
      | exact completed_1202120 k
      | exact completed_1202121 k
      | exact completed_1210101 k
      | exact completed_1210102 k
      | exact completed_1210120 k
      | exact completed_1210121 k
      | exact completed_1210201 k
      | exact completed_1210202 k
      | exact completed_1210210 k
      | exact completed_1210212 k
      | exact completed_1212010 k
      | exact completed_1212012 k
      | exact completed_1212020 k
      | exact completed_1212021 k
      | exact completed_1212101 k
      | exact completed_1212102 k
      | exact completed_1212120 k
      | exact completed_1212121 k
      | exact unseen_1010101 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
