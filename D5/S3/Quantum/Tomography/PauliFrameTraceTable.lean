/- GID: D5/S3/Quantum/Tomography/PauliFrameTraceTable
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/PauliFrameTraceTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two labelled Pauli frames have the same finite trace table, with a non-real complex-frame witness. -/

/-
proof_shape: trace_table: content; escape_witness: the explicit finite Pauli trace computation
  across both frame choices; admission_basis: escape-witness.
proof_shape: complex_frame_nonreal_witness: content; escape_witness: the explicit nonzero
  imaginary matrix entry of the complex frame; admission_basis: escape-witness.
Direct frozen dependency: D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.word_trace_pair.
Escape audit unfinished for both public theorems; linked issue:
https://github.com/the-omega-institute/trureturing/issues/29460
The full Jordan-closure dimension claims from the source atom remain open.
-/

import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace D5.S3.Quantum.Tomography.PauliFrameTraceTable

open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information
open D5.S3.Quantum.FiniteDimensional

private abbrev Op := Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ
private abbrev Bits := Fin 2 × Fin 2

private def eps (b : Fin 2) : ℂ := if b = 0 then 1 else -1

private def proj (A B C : Fin 2 → Pauli) (st : Bits) : Op :=
  (1 / 4 : ℂ) • ((1 : Op) + eps st.1 • wordOp A + eps st.2 • wordOp B +
    (eps st.1 * eps st.2) • wordOp C)

private def E (st : Bits) : Op :=
  proj ![Pauli.Z, Pauli.I] ![Pauli.I, Pauli.Z] ![Pauli.Z, Pauli.Z] st

private def F (st : Bits) : Op :=
  proj ![Pauli.X, Pauli.I] ![Pauli.I, Pauli.X] ![Pauli.X, Pauli.X] st

private def Gr (st : Bits) : Op :=
  proj ![Pauli.X, Pauli.Z] ![Pauli.Z, Pauli.X] ![Pauli.Y, Pauli.Y] st

private def Gc (st : Bits) : Op :=
  proj ![Pauli.Y, Pauli.I] ![Pauli.I, Pauli.Y] ![Pauli.Y, Pauli.Y] st

private def yI : Fin 2 → Pauli := ![Pauli.Y, Pauli.I]

/-- The two labelled triples use the same first two contexts and differ only in G. -/
def frame (c : Bool) (i : Fin 3) (st : Fin 2 × Fin 2) :
    Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  if i = 0 then E st else if i = 1 then F st else if c then Gr st else Gc st

private lemma word_trace (p : Fin 2 → Pauli) :
    Matrix.trace (wordOp p) = if p = (fun _ => Pauli.I) then 4 else 0 := by
  have h := word_trace_pair p (fun _ => Pauli.I)
  rw [word_one, mul_one] at h
  simpa only [show (2 : ℂ) ^ 2 = 4 by norm_num] using h

private lemma word_trace_zero {p : Fin 2 → Pauli} (h : ∃ i, p i ≠ Pauli.I) :
    Matrix.trace (wordOp p) = 0 := by
  rw [word_trace]
  split_ifs with hp
  · obtain ⟨i, hi⟩ := h
    exact False.elim (hi (congrFun hp i))
  · rfl

/-- Both real and complex choices of the third context give the same twelve-entry table. -/
theorem trace_table (c : Bool) (i j : Fin 3) (st uv : Fin 2 × Fin 2) :
    Matrix.trace (frame c i st * frame c j uv) =
      if i = j then (if st = uv then (1 : ℂ) else 0) else (1 / 4 : ℂ) := by
  have hZI : Matrix.trace (wordOp ![Pauli.Z, Pauli.I]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hIZ : Matrix.trace (wordOp ![Pauli.I, Pauli.Z]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  have hZZ : Matrix.trace (wordOp ![Pauli.Z, Pauli.Z]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hXI : Matrix.trace (wordOp ![Pauli.X, Pauli.I]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hIX : Matrix.trace (wordOp ![Pauli.I, Pauli.X]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  have hXX : Matrix.trace (wordOp ![Pauli.X, Pauli.X]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hXZ : Matrix.trace (wordOp ![Pauli.X, Pauli.Z]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hZX : Matrix.trace (wordOp ![Pauli.Z, Pauli.X]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  have hYY : Matrix.trace (wordOp ![Pauli.Y, Pauli.Y]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hYI : Matrix.trace (wordOp ![Pauli.Y, Pauli.I]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hIY : Matrix.trace (wordOp ![Pauli.I, Pauli.Y]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  fin_cases c <;> fin_cases i <;> fin_cases j <;> fin_cases st <;> fin_cases uv <;>
    simp [frame, E, F, Gr, Gc, proj, eps, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_one, word_trace_pair, word_trace, hZI, hIZ, hZZ, hXI, hIX,
      hXX, hXZ, hZX, hYY, hYI, hIY] <;>
    norm_num

/-- The complex third context has an entry with nonzero imaginary part. -/
theorem complex_frame_nonreal_witness :
    ∃ x y : Fin 2 → Fin 2, (wordOp yI x y).im ≠ 0 := by
  refine ⟨![0, 0], ![1, 0], ?_⟩
  norm_num [yI, wordOp, tensorOp, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_two]

#print axioms frame
#print axioms trace_table
#print axioms complex_frame_nonreal_witness

end D5.S3.Quantum.Tomography.PauliFrameTraceTable
