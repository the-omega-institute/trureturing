/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Certificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Certificate
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
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOne
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

private theorem completed_2010101 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010102 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010120 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010121 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010201 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010202 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010210 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2010212 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012010 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012012 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012020 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012021 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012101 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012102 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012120 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2012121 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020101 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020102 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020120 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020121 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020201 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020202 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020210 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2020212 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021010 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021012 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021020 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021021 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021201 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021202 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021210 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2021212 : ∀ k : Fin 21,
    classCount (true, true) ![2, 0, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101010 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101012 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101020 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101021 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101201 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101202 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101210 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2101212 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102010 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102012 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102020 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102021 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102101 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102102 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102120 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2102121 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120101 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120102 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120120 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120121 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120201 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120202 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120210 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2120212 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121010 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121012 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121020 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121021 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121201 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121202 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121210 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

private theorem completed_2121212 : ∀ k : Fin 21,
    classCount (true, true) ![2, 1, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized, (full_row 7 _).1, (full_row 7 _).2]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 4000000 in
private theorem row_counts_two : ∀ s p, Valid s p → p 0 = 2 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst k
  change p0 = (2 : Fin 3) at hfirst
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
      | exact completed_2010101 k
      | exact completed_2010102 k
      | exact completed_2010120 k
      | exact completed_2010121 k
      | exact completed_2010201 k
      | exact completed_2010202 k
      | exact completed_2010210 k
      | exact completed_2010212 k
      | exact completed_2012010 k
      | exact completed_2012012 k
      | exact completed_2012020 k
      | exact completed_2012021 k
      | exact completed_2012101 k
      | exact completed_2012102 k
      | exact completed_2012120 k
      | exact completed_2012121 k
      | exact completed_2020101 k
      | exact completed_2020102 k
      | exact completed_2020120 k
      | exact completed_2020121 k
      | exact completed_2020201 k
      | exact completed_2020202 k
      | exact completed_2020210 k
      | exact completed_2020212 k
      | exact completed_2021010 k
      | exact completed_2021012 k
      | exact completed_2021020 k
      | exact completed_2021021 k
      | exact completed_2021201 k
      | exact completed_2021202 k
      | exact completed_2021210 k
      | exact completed_2021212 k
      | exact completed_2101010 k
      | exact completed_2101012 k
      | exact completed_2101020 k
      | exact completed_2101021 k
      | exact completed_2101201 k
      | exact completed_2101202 k
      | exact completed_2101210 k
      | exact completed_2101212 k
      | exact completed_2102010 k
      | exact completed_2102012 k
      | exact completed_2102020 k
      | exact completed_2102021 k
      | exact completed_2102101 k
      | exact completed_2102102 k
      | exact completed_2102120 k
      | exact completed_2102121 k
      | exact completed_2120101 k
      | exact completed_2120102 k
      | exact completed_2120120 k
      | exact completed_2120121 k
      | exact completed_2120201 k
      | exact completed_2120202 k
      | exact completed_2120210 k
      | exact completed_2120212 k
      | exact completed_2121010 k
      | exact completed_2121012 k
      | exact completed_2121020 k
      | exact completed_2121021 k
      | exact completed_2121201 k
      | exact completed_2121202 k
      | exact completed_2121210 k
      | exact completed_2121212 k
end

open private row_counts_zero from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZero
open private row_counts_one from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOne

private theorem row_counts (s : Seen) (p : PairRow) (hp : Valid s p) (k : Fin 21) :
    classCount s p k = transfer (boundaryClass s p) k := by
  have h : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide +kernel
  rcases h (p 0) with hzero | hone | htwo
  · exact row_counts_zero s p hp hzero k
  · exact row_counts_one s p hp hone k
  · exact row_counts_two s p hp htwo k

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
