/- GID: D5/S3/Quantum/Tomography/PauliFrameTraceTable
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/PauliFrameTraceTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The labelled Pauli frame triples have equal two-point tables but different Jordan closures. -/

import Mathlib
import D5.S3.Quantum.Tomography.RankOneContextCommutator

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace D5.S3.Quantum.Tomography.PauliFrameTraceTable

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.RankOneContextCommutator

private abbrev Bits := Fin 2 × Fin 2
private abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ
private abbrev H4 := HermitianSpace 4

private def I4 : Mat4 := 1
private def ZI : Mat4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
private def IZ : Mat4 := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]
private def ZZ : Mat4 := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]
private def XI : Mat4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
private def IX : Mat4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
private def XX : Mat4 := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
private def XZ : Mat4 := !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0]
private def ZX : Mat4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]
private def YY : Mat4 := !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0]
private def YI : Mat4 := !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I; Complex.I, 0, 0, 0; 0, Complex.I, 0, 0]
private def IY : Mat4 := !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, -Complex.I; 0, 0, Complex.I, 0]

private def eps (b : Fin 2) : ℂ := if b = 0 then 1 else -1

private def projMat (A B C : Mat4) (st : Bits) : Mat4 :=
  (1 / 4 : ℂ) • (I4 + eps st.1 • A + eps st.2 • B +
    (eps st.1 * eps st.2) • C)

private def E (st : Bits) : Mat4 := projMat ZI IZ ZZ st
private def F (st : Bits) : Mat4 := projMat XI IX XX st
private def Gr (st : Bits) : Mat4 := projMat XZ ZX YY st
private def Gc (st : Bits) : Mat4 := projMat YI IY YY st

private lemma E_hermitian (st : Bits) : (E st).IsHermitian := by
  fin_cases st <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [E, projMat, I4, ZI, IZ, ZZ, eps, Matrix.IsHermitian]

private lemma F_hermitian (st : Bits) : (F st).IsHermitian := by
  fin_cases st <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [F, projMat, I4, XI, IX, XX, eps, Matrix.IsHermitian]

private lemma Gr_hermitian (st : Bits) : (Gr st).IsHermitian := by
  fin_cases st <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Gr, projMat, I4, XZ, ZX, YY, eps, Matrix.IsHermitian]

private lemma Gc_hermitian (st : Bits) : (Gc st).IsHermitian := by
  fin_cases st <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Gc, projMat, I4, YI, IY, YY, eps, Matrix.IsHermitian]

private def hOf (A : Mat4) (hA : A.IsHermitian) : H4 := ⟨A, by
  simpa only [Matrix.star_eq_conjTranspose] using hA⟩

private def frameMat (c : Bool) (i : Fin 3) (st : Bits) : Mat4 :=
  if i = 0 then E st else if i = 1 then F st else if c then Gr st else Gc st

def frame (c : Bool) (i : Fin 3) (st : Bits) : H4 :=
  if i = 0 then hOf (E st) (E_hermitian st) else
  if i = 1 then hOf (F st) (F_hermitian st) else
  if c then hOf (Gr st) (Gr_hermitian st) else hOf (Gc st) (Gc_hermitian st)

private lemma frame_val (c : Bool) (i : Fin 3) (st : Bits) :
    (frame c i st).1 = frameMat c i st := by
  simp [frame, frameMat]

private lemma frame_rank_one (c : Bool) (i : Fin 3) (st : Bits) :
    IsNormalizedRankOneProjection (frameMat c i st) := by
  fin_cases c <;> fin_cases i <;> fin_cases st <;>
    simp [frameMat, E, F, Gr, Gc, projMat, I4, ZI, IZ, ZZ, XI, IX, XX,
      XZ, ZX, YY, YI, IY, eps, Matrix.IsHermitian, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.trace, Matrix.conjTranspose_apply] <;>
    norm_num

private lemma frame_resolves (c : Bool) (i : Fin 3) :
    ∑ st : Bits, frameMat c i st = 1 := by
  fin_cases c <;> fin_cases i <;>
    simp [frameMat, E, F, Gr, Gc, projMat, I4, ZI, IZ, ZZ, XI, IX, XX,
      XZ, ZX, YY, YI, IY, eps, Fin.sum_prod_type, Fin.sum_univ_two,
      Matrix.add_assoc, Matrix.smul_add] <;>
    norm_num

theorem complete_rank_one_projector_frames (c : Bool) (i : Fin 3) :
    (∀ st : Bits, IsNormalizedRankOneProjection (frameMat c i st)) ∧
      ∑ st : Bits, frameMat c i st = 1 :=
  ⟨frame_rank_one c i, frame_resolves c i⟩

theorem trace_table (c : Bool) (i j : Fin 3) (st uv : Bits) :
    Matrix.trace ((frame c i st).1 * (frame c j uv).1) =
      if i = j then (if st = uv then (1 : ℂ) else 0) else (1 / 4 : ℂ) := by
  rw [frame_val, frame_val]
  fin_cases c <;> fin_cases i <;> fin_cases j <;> fin_cases st <;> fin_cases uv <;>
    simp [frameMat, E, F, Gr, Gc, projMat, I4, ZI, IZ, ZZ, XI, IX, XX,
      XZ, ZX, YY, YI, IY, eps, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.trace, Matrix.trace_mul_cycle] <;>
    norm_num

private def jordan (A B : H4) : H4 := by
  refine ⟨(1 / 2 : ℂ) • (A.1 * B.1 + B.1 * A.1), ?_⟩
  change star ((1 / 2 : ℂ) • (A.1 * B.1 + B.1 * A.1)) = _
  have hA : A.1ᴴ = A.1 := by simpa only [Matrix.star_eq_conjTranspose] using A.2
  have hB : B.1ᴴ = B.1 := by simpa only [Matrix.star_eq_conjTranspose] using B.2
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA, hB,
    Complex.star_def, map_inv₀, conj_ofReal, Complex.conj_ofReal,
    one_div, invOf_eq_inv]
  ring

inductive JWord where
  | leaf : Fin 3 × Bits → JWord
  | product : JWord → JWord → JWord

private def evalWord (c : Bool) : JWord → H4
  | .leaf q => frame c q.1 q.2
  | .product u v => jordan (evalWord c u) (evalWord c v)

def Jcl (c : Bool) : Submodule ℝ H4 :=
  Submodule.span ℝ (Set.range (evalWord c))

private def realPartSubspace : Submodule ℝ H4 where
  carrier := {A | ∀ i j, (A.1 i j).im = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j
    simp [Matrix.add_apply, hA i j, hB i j]
  smul_mem' := by
    intro r A hA i j
    simp [Matrix.smul_apply, Complex.mul_im, hA i j]

def H4R : Submodule ℝ H4 := realPartSubspace
def H4C : Submodule ℝ H4 := ⊤

private def d00 : H4 := hOf (Matrix.single 0 0 1) (by simp [Matrix.IsHermitian])
private def d01 : H4 := hOf (Matrix.single 1 1 1) (by simp [Matrix.IsHermitian])
private def d10 : H4 := hOf (Matrix.single 2 2 1) (by simp [Matrix.IsHermitian])
private def d11 : H4 := hOf (Matrix.single 3 3 1) (by simp [Matrix.IsHermitian])

private def redge (i j : Fin 4) : H4 := hOf
  (Matrix.single i j 1 + Matrix.single j i 1) (by
    ext a b
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, Matrix.single_apply,
      eq_comm, and_comm, and_left_comm, and_assoc])

private def iedge (i j : Fin 4) : H4 := hOf
  (Complex.I • Matrix.single i j 1 - Complex.I • Matrix.single j i 1) (by
    ext a b
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, Matrix.single_apply,
      Complex.star_def, eq_comm, and_comm, and_left_comm, and_assoc])

private def realBasis : Fin 10 → H4
  | 0 => d00 | 1 => d01 | 2 => d10 | 3 => d11
  | 4 => redge 0 1 | 5 => redge 0 2 | 6 => redge 0 3
  | 7 => redge 1 2 | 8 => redge 1 3 | 9 => redge 2 3

private def complexBasis : Fin 16 → H4
  | 0 => d00 | 1 => d01 | 2 => d10 | 3 => d11
  | 4 => redge 0 1 | 5 => redge 0 2 | 6 => redge 0 3
  | 7 => redge 1 2 | 8 => redge 1 3 | 9 => redge 2 3
  | 10 => iedge 0 1 | 11 => iedge 0 2 | 12 => iedge 0 3
  | 13 => iedge 1 2 | 14 => iedge 1 3 | 15 => iedge 2 3

private lemma realBasis_linearIndependent : LinearIndependent ℝ realBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c h j
  have h' := congrArg (fun A : H4 => A.1) h
  have hentry (a b : Fin 4) := congrFun (congrFun h' a) b
  fin_cases j <;>
    first
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 0
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 1
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 2 2
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 3 3
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 1
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 2
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 3
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 2
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 3
    | simpa [realBasis, d00, d01, d10, d11, redge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 2 3

private lemma complexBasis_linearIndependent : LinearIndependent ℝ complexBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c h j
  have h' := congrArg (fun A : H4 => A.1) h
  have hentry (a b : Fin 4) := congrFun (congrFun h' a) b
  fin_cases j <;>
    first
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 0
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 1
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 2 2
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 3 3
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 1
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 2
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 0 3
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 2
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 3
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 2 3
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 1 0
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 2 0
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 3 0
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 2 1
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 3 1
    | simpa [complexBasis, d00, d01, d10, d11, redge, iedge, Matrix.single_apply,
        Matrix.sum_apply, Matrix.smul_apply] using hentry 3 2

theorem real_closure_finrank : Module.finrank ℝ H4R = 10 := by
  rw [H4R]
  apply (Submodule.finrank_span_eq_card realBasis_linearIndependent).trans
  rfl

theorem complex_closure_finrank : Module.finrank ℝ H4C = 16 := by
  rw [H4C]
  simpa using hermitian_space_finrank 4

theorem jordan_closure_real : Jcl true = H4R := by
  sorry

theorem jordan_closure_complex : Jcl false = H4C := by
  sorry

theorem labelled_two_point_tables_do_not_determine_dimension :
    (Jcl true = H4R ∧ Module.finrank ℝ H4R = 10) ∧
      (Jcl false = H4C ∧ Module.finrank ℝ H4C = 16) ∧
      (∀ c i j st uv,
        Matrix.trace ((frame c i st).1 * (frame c j uv).1) =
          if i = j then (if st = uv then (1 : ℂ) else 0) else (1 / 4 : ℂ)) := by
  exact ⟨⟨jordan_closure_real, real_closure_finrank⟩,
    ⟨jordan_closure_complex, complex_closure_finrank⟩, trace_table⟩

#print axioms complete_rank_one_projector_frames
#print axioms trace_table
#print axioms jordan_closure_real
#print axioms jordan_closure_complex
#print axioms labelled_two_point_tables_do_not_determine_dimension

end D5.S3.Quantum.Tomography.PauliFrameTraceTable
