/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneD
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOneD
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
DIRECT_FROZEN_DEPENDENCIES
DECLARATION_CONSUMERS
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open private class_fibres_normalized from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Fibres
open HardinA233255ShapeSymmetry (full_row)

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

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
