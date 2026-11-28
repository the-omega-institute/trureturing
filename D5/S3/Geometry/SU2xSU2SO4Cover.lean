/- GID: D5/S3/Geometry/SU2xSU2SO4Cover
   generality: G
   mirror-B: none(waiver:covered-by-pati-salam-unification4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The left and right actions of determinant-one unitary matrices on the real quaternion coordinates give an oriented orthogonal action in dimension four. -/

import OmegaBuild.Commands
import D5.S3.Geometry.SU2EulerCover
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Omega original.

The left and right actions of determinant-one unitary matrices on the real
quaternion coordinates give an oriented orthogonal action in dimension four. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OmegaMath.SU2xSU2SO4Cover

open Matrix

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev C2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev R4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Coordinates in the basis consisting of the identity and the three Pauli
matrices multiplied by the imaginary unit, in Pauli order. -/
def quaternionMatrix (x : Fin 4 → ℝ) : C2 :=
  !![⟨x 0, x 3⟩, ⟨x 2, x 1⟩; ⟨-x 2, x 1⟩, ⟨x 0, -x 3⟩]

private def coordinates (A : C2) : Fin 4 → ℝ :=
  ![(A 0 0).re, (A 0 1).im, (A 0 1).re, (A 0 0).im]

private theorem coordinates_quaternionMatrix (x : Fin 4 → ℝ) :
    coordinates (quaternionMatrix x) = x := by
  funext i
  fin_cases i <;> rfl

private theorem quaternionMatrix_injective : Function.Injective quaternionMatrix :=
  Function.LeftInverse.injective coordinates_quaternionMatrix

private def normSq (x : Fin 4 → ℝ) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

theorem quaternionMatrix_det (x : Fin 4 → ℝ) :
    (quaternionMatrix x).det = ((∑ i, x i ^ 2 : ℝ) : ℂ) := by
  rw [quaternionMatrix, det_fin_two_of]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Fin.sum_univ_succ, -Complex.ofReal_pow] <;> ring

private theorem quaternionMatrix_su2 (U : SU2) : quaternionMatrix (coordinates U) = (U : C2) := by
  have hU := (mem_specialUnitaryGroup_iff.mp U.property)
  have huv : (U : C2) * (U : C2)ᴴ = 1 := mem_unitaryGroup_iff.mp hU.1
  have hadj : (U : C2).adjugate * (U : C2) = 1 := by
    rw [adjugate_mul, hU.2, one_smul]
  have hinv : (U : C2)ᴴ = (U : C2).adjugate := by
    calc
      _ = ((U : C2).adjugate * (U : C2)) * (U : C2)ᴴ := by rw [hadj, one_mul]
      _ = _ := by rw [Matrix.mul_assoc, huv, mul_one]
  rw [adjugate_fin_two] at hinv
  have h11 : (U : C2) 1 1 = star ((U : C2) 0 0) := by
    simpa using (congrArg (fun A : C2 => A 0 0) hinv).symm
  have h10 : (U : C2) 1 0 = -star ((U : C2) 0 1) := by
    simpa using (congrArg Neg.neg (congrArg (fun A : C2 => A 1 0) hinv)).symm
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [coordinates, quaternionMatrix, h11, h10]

private theorem normSq_su2 (U : SU2) : normSq (coordinates U) = 1 := by
  have hu := quaternionMatrix_det (coordinates U)
  rw [quaternionMatrix_su2, (mem_specialUnitaryGroup_iff.mp U.property).2] at hu
  simpa [normSq, Fin.sum_univ_succ, ← Complex.ofReal_pow, add_assoc] using (congrArg Complex.re hu).symm

private def leftMatrix (x : Fin 4 → ℝ) : R4 :=
  !![x 0, -x 1, -x 2, -x 3;
     x 1, x 0, x 3, -x 2;
     x 2, -x 3, x 0, x 1;
     x 3, x 2, -x 1, x 0]

private def rightMatrix (x : Fin 4 → ℝ) : R4 :=
  !![x 0, -x 1, -x 2, -x 3;
     x 1, x 0, -x 3, x 2;
     x 2, x 3, x 0, -x 1;
     x 3, -x 2, x 1, x 0]

private theorem quaternionMatrix_left (x y : Fin 4 → ℝ) :
    quaternionMatrix (leftMatrix x *ᵥ y) = quaternionMatrix x * quaternionMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [leftMatrix, quaternionMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring

private theorem quaternionMatrix_right (x y : Fin 4 → ℝ) :
    quaternionMatrix (rightMatrix y *ᵥ x) = quaternionMatrix x * quaternionMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [rightMatrix, quaternionMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring

private theorem leftMatrix_transpose_mul (x : Fin 4 → ℝ) :
    (leftMatrix x)ᵀ * leftMatrix x = normSq x • (1 : R4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, normSq, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem rightMatrix_transpose_mul (x : Fin 4 → ℝ) :
    (rightMatrix x)ᵀ * rightMatrix x = normSq x • (1 : R4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightMatrix, normSq, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem leftMatrix_det (x : Fin 4 → ℝ) : (leftMatrix x).det = normSq x ^ 2 := by
  simp only [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Matrix.submatrix_apply]
  simp [leftMatrix, normSq, Fin.succAbove, Fin.lt_def]
  ring

private theorem rightMatrix_det (x : Fin 4 → ℝ) : (rightMatrix x).det = normSq x ^ 2 := by
  simp only [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Matrix.submatrix_apply]
  simp [rightMatrix, normSq, Fin.succAbove, Fin.lt_def]
  ring

/-- The real coordinate matrix of the action by left multiplication by (L)
and right multiplication by the conjugate transpose of (R). -/
def so4OfSU2xSU2 (L R : SU2) : R4 :=
  leftMatrix (coordinates L) * rightMatrix (coordinates (star R : SU2))

theorem so4OfSU2xSU2_action (L R : SU2) (x : Fin 4 → ℝ) :
    quaternionMatrix (so4OfSU2xSU2 L R *ᵥ x) = (L : C2) * quaternionMatrix x * (R : C2)ᴴ := by
  rw [so4OfSU2xSU2, ← Matrix.mulVec_mulVec, quaternionMatrix_left, quaternionMatrix_right,
    quaternionMatrix_su2, quaternionMatrix_su2, Matrix.mul_assoc]
  rfl

theorem so4OfSU2xSU2_one : so4OfSU2xSU2 1 1 = 1 := by
  apply Matrix.mulVec_injective
  funext x
  apply quaternionMatrix_injective
  simp [so4OfSU2xSU2_action]

theorem so4OfSU2xSU2_mul (L R L' R' : SU2) :
    so4OfSU2xSU2 (L * L') (R * R') = so4OfSU2xSU2 L R * so4OfSU2xSU2 L' R' := by
  apply Matrix.mulVec_injective
  funext x
  apply quaternionMatrix_injective
  rw [← Matrix.mulVec_mulVec, so4OfSU2xSU2_action, so4OfSU2xSU2_action, so4OfSU2xSU2_action]
  change ((L : C2) * (L' : C2)) * quaternionMatrix x * ((R : C2) * (R' : C2))ᴴ =
    (L : C2) * ((L' : C2) * quaternionMatrix x * (R' : C2)ᴴ) * (R : C2)ᴴ
  simp [conjTranspose_mul, Matrix.mul_assoc]

theorem so4OfSU2xSU2_orthogonal (L R : SU2) :
    (so4OfSU2xSU2 L R)ᵀ * so4OfSU2xSU2 L R = 1 := by
  unfold so4OfSU2xSU2
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
    (leftMatrix (coordinates L))ᵀ, leftMatrix_transpose_mul, normSq_su2, one_smul, one_mul,
    rightMatrix_transpose_mul, normSq_su2, one_smul]

theorem so4OfSU2xSU2_det_one (L R : SU2) : (so4OfSU2xSU2 L R).det = 1 := by
  rw [so4OfSU2xSU2, Matrix.det_mul, leftMatrix_det, rightMatrix_det, normSq_su2, normSq_su2]
  norm_num

/-- The nonidentity scalar of determinant one in dimension two. -/
def su2NegOne : SU2 :=
  ⟨-(1 : C2), mem_specialUnitaryGroup_iff.mpr
    ⟨mem_unitaryGroup_iff'.mpr (by simp), by simp [Matrix.det_neg]⟩⟩

private theorem quaternionMatrix_scalar (s : ℝ) :
    quaternionMatrix ![s, 0, 0, 0] = (s : ℂ) • (1 : C2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quaternionMatrix]

theorem so4OfSU2xSU2_kernel (L R : SU2) :
    so4OfSU2xSU2 L R = 1 ↔ (L = 1 ∧ R = 1) ∨ (L = su2NegOne ∧ R = su2NegOne) := by
  constructor
  · intro h
    have act (x : Fin 4 → ℝ) : (L : C2) * quaternionMatrix x * (R : C2)ᴴ =
        quaternionMatrix x := by
      rw [← so4OfSU2xSU2_action, h, Matrix.one_mulVec]
    have hu : (R : C2)ᴴ * (R : C2) = 1 :=
      mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp R.property).1
    have LR : L = R := by
      apply Subtype.ext
      have he := act ![1, 0, 0, 0]
      rw [quaternionMatrix_scalar, Complex.ofReal_one, one_smul, mul_one] at he
      simpa [Matrix.mul_assoc, hu] using congrArg (fun A : C2 => A * (R : C2)) he
    subst R
    have hcomm : leftMatrix (coordinates L) = rightMatrix (coordinates L) := by
      apply Matrix.mulVec_injective
      funext x
      apply quaternionMatrix_injective
      rw [quaternionMatrix_left, quaternionMatrix_right, quaternionMatrix_su2]
      simpa [Matrix.mul_assoc, hu] using congrArg (fun A : C2 => A * (L : C2)) (act x)
    have h1 : coordinates L 1 = 0 := by
      have he := congrArg (fun A : R4 => A 2 3) hcomm
      simp [leftMatrix, rightMatrix] at he
      linarith
    have h2 : coordinates L 2 = 0 := by
      have he := congrArg (fun A : R4 => A 3 1) hcomm
      simp [leftMatrix, rightMatrix] at he
      linarith
    have h3 : coordinates L 3 = 0 := by
      have he := congrArg (fun A : R4 => A 1 2) hcomm
      simp [leftMatrix, rightMatrix] at he
      linarith
    have hsq : coordinates L 0 ^ 2 = 1 := by
      simpa [normSq, h1, h2, h3] using normSq_su2 L
    have hcoord : coordinates L = ![coordinates L 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> simp [h1, h2, h3]
    have hscalar : (L : C2) = (coordinates L 0 : ℂ) • (1 : C2) := by
      conv_lhs => rw [← quaternionMatrix_su2 L, hcoord]
      exact quaternionMatrix_scalar _
    rcases (sq_eq_one_iff.mp hsq) with hpos | hneg
    · left
      have hone : L = 1 := Subtype.ext (by simpa [hpos] using hscalar)
      exact ⟨hone, hone⟩
    · right
      have hnegative : L = su2NegOne := Subtype.ext (by simpa [hneg, su2NegOne] using hscalar)
      exact ⟨hnegative, hnegative⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact so4OfSU2xSU2_one
    · apply Matrix.mulVec_injective
      funext x
      apply quaternionMatrix_injective
      rw [so4OfSU2xSU2_action, Matrix.one_mulVec]
      change -(1 : C2) * quaternionMatrix x * (-(1 : C2))ᴴ = quaternionMatrix x
      simp

/-- The quaternion action as a homomorphism into the real special orthogonal group. -/
def so4CoverHom : SU2 × SU2 →* Matrix.specialOrthogonalGroup (Fin 4) ℝ where
  toFun x := ⟨so4OfSU2xSU2 x.1 x.2, mem_specialOrthogonalGroup_iff.mpr
    ⟨(mem_orthogonalGroup_iff' (Fin 4) ℝ).mpr (so4OfSU2xSU2_orthogonal _ _), so4OfSU2xSU2_det_one _ _⟩⟩
  map_one' := Subtype.ext so4OfSU2xSU2_one
  map_mul' x y := Subtype.ext (so4OfSU2xSU2_mul x.1 x.2 y.1 y.2)

private def quaternionUnit (x : Fin 4 → ℝ) (hx : normSq x = 1) : SU2 :=
  ⟨quaternionMatrix x, mem_specialUnitaryGroup_iff.mpr (by
    constructor
    · apply mem_unitaryGroup_iff'.mpr
      have h :
          (quaternionMatrix x)ᴴ * quaternionMatrix x = (normSq x : ℂ) • (1 : C2) := by
        ext i j
        fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
          simp [quaternionMatrix, normSq, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
            Complex.mul_im, -Complex.ofReal_pow] <;> ring
      simpa [hx, Matrix.star_eq_conjTranspose] using h
    · rw [quaternionMatrix_det]
      simpa [normSq, Fin.sum_univ_succ, add_assoc, -Complex.ofReal_pow] using
        congrArg Complex.ofReal hx)⟩

private theorem quaternionMatrix_conjTranspose (x : Fin 4 → ℝ) :
    (quaternionMatrix x)ᴴ = quaternionMatrix ![x 0, -x 1, -x 2, -x 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]

private abbrev R3 := Matrix (Fin 3) (Fin 3) ℝ

private def fixScalar (B : R3) : R4 :=
  Matrix.of (Fin.cons (Fin.cons 1 0) fun i => Fin.cons 0 (B i))

private theorem fixScalar_mul (B C : R3) : fixScalar (B * C) = fixScalar B * fixScalar C := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [fixScalar, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem so4_rotZ (θ : ℝ) :
    ∃ U : SU2, so4OfSU2xSU2 U U = fixScalar (SU2EulerCover.rotZ3 θ) := by
  let x : Fin 4 → ℝ := ![Real.cos (θ / 2), 0, 0, -Real.sin (θ / 2)]
  have hx : normSq x = 1 := by
    simp [normSq, x, add_comm]
  refine ⟨quaternionUnit x hx, ?_⟩
  change leftMatrix (coordinates (quaternionMatrix x)) *
    rightMatrix (coordinates (quaternionMatrix x)ᴴ) = _
  rw [quaternionMatrix_conjTranspose, coordinates_quaternionMatrix, coordinates_quaternionMatrix]
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    calc
      Real.cos θ = Real.cos (2 * (θ / 2)) := by
        congr 1
        ring
      _ = _ := by
        rw [Real.cos_two_mul]
        linarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    calc
      Real.sin θ = Real.sin (2 * (θ / 2)) := by
        congr 1
        ring
      _ = _ := Real.sin_two_mul _
  rw [show fixScalar (SU2EulerCover.rotZ3 θ) =
      !![1, 0, 0, 0;
        0, Real.cos θ, -Real.sin θ, 0;
        0, Real.sin θ, Real.cos θ, 0;
        0, 0, 0, 1] from by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, rightMatrix, x, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs] <;>
    nlinarith only [Real.sin_sq_add_cos_sq (θ / 2)]

private theorem so4_rotY (θ : ℝ) :
    ∃ U : SU2, so4OfSU2xSU2 U U = fixScalar (SU2EulerCover.rotY3 θ) := by
  let x : Fin 4 → ℝ := ![Real.cos (θ / 2), 0, -Real.sin (θ / 2), 0]
  have hx : normSq x = 1 := by
    simp [normSq, x, add_comm]
  refine ⟨quaternionUnit x hx, ?_⟩
  change leftMatrix (coordinates (quaternionMatrix x)) *
    rightMatrix (coordinates (quaternionMatrix x)ᴴ) = _
  rw [quaternionMatrix_conjTranspose, coordinates_quaternionMatrix, coordinates_quaternionMatrix]
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    calc
      Real.cos θ = Real.cos (2 * (θ / 2)) := by
        congr 1
        ring
      _ = _ := by
        rw [Real.cos_two_mul]
        linarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    calc
      Real.sin θ = Real.sin (2 * (θ / 2)) := by
        congr 1
        ring
      _ = _ := Real.sin_two_mul _
  rw [show fixScalar (SU2EulerCover.rotY3 θ) =
      !![1, 0, 0, 0;
        0, Real.cos θ, 0, Real.sin θ;
        0, 0, 1, 0;
        0, -Real.sin θ, 0, Real.cos θ] from by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, rightMatrix, x, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs] <;>
    nlinarith only [Real.sin_sq_add_cos_sq (θ / 2)]

private theorem so4_stabilizer (B : R3) (hB : Bᵀ * B = 1) (hd : B.det = 1) :
    ∃ R : SU2, so4OfSU2xSU2 R R = fixScalar B := by
  obtain ⟨α, β, γ, h⟩ := SU2EulerCover.so3_euler B hB hd
  obtain ⟨U, hU⟩ := so4_rotZ α
  obtain ⟨V, hV⟩ := so4_rotY β
  obtain ⟨W, hW⟩ := so4_rotZ γ
  refine ⟨U * V * W, ?_⟩
  rw [so4OfSU2xSU2_mul, so4OfSU2xSU2_mul, hU, hV, hW, h, fixScalar_mul, fixScalar_mul]

private theorem mulVec_scalarBasis (M : R4) :
    M *ᵥ ![1, 0, 0, 0] = fun i => M i 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem fixScalar_det (B : R3) : (fixScalar B).det = B.det := by
  rw [det_succ_row_zero]
  simp [fixScalar, Fin.sum_univ_succ, Fin.zero_succAbove, Matrix.submatrix]
  rfl

private theorem so4_surjective (M : R4) (hM : Mᵀ * M = 1) (hd : M.det = 1) :
    ∃ L R : SU2, so4OfSU2xSU2 L R = M := by
  let x : Fin 4 → ℝ := fun i => M i 0
  have hx : normSq x = 1 := by
    have h := congrArg (fun A : R4 => A 0 0) hM
    simpa [normSq, x, Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h
  let P := quaternionUnit x hx
  have hP : so4OfSU2xSU2 P 1 *ᵥ ![1, 0, 0, 0] = x := by
    apply quaternionMatrix_injective
    rw [so4OfSU2xSU2_action, quaternionMatrix_scalar]
    simp [P, quaternionUnit]
  let N := so4OfSU2xSU2 P⁻¹ 1 * M
  have hcol : ∀ i, N i 0 = (![1, 0, 0, 0] : Fin 4 → ℝ) i := by
    have hvec : N *ᵥ ![1, 0, 0, 0] = ![1, 0, 0, 0] := by
      change (so4OfSU2xSU2 P⁻¹ 1 * M) *ᵥ ![1, 0, 0, 0] = _
      rw [← Matrix.mulVec_mulVec, mulVec_scalarBasis, show (fun i => M i 0) = x by rfl,
        ← hP, Matrix.mulVec_mulVec]
      rw [← so4OfSU2xSU2_mul, inv_mul_cancel, mul_one, so4OfSU2xSU2_one, Matrix.one_mulVec]
    rw [mulVec_scalarBasis] at hvec
    exact congrFun hvec
  have hN : Nᵀ * N = 1 := by
    dsimp only [N]
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
      (so4OfSU2xSU2 P⁻¹ 1)ᵀ, so4OfSU2xSU2_orthogonal, one_mul, hM]
  have hrow (j : Fin 3) : N 0 j.succ = 0 := by
    have h := congrArg (fun A : R4 => A 0 j.succ) hN
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, hcol, Matrix.one_apply, (Fin.succ_ne_zero j).symm] using h
  let B := N.submatrix Fin.succ Fin.succ
  have hNB : N = fixScalar B := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [fixScalar] using hcol 0
    · simpa [fixScalar] using hrow j
    · change N i.succ 0 = 0
      exact (hcol i.succ).trans (by fin_cases i <;> rfl)
    · rfl
  have hB : Bᵀ * B = 1 := by
    ext i j
    have h := congrArg (fun A : R4 => A i.succ j.succ) hN
    simpa [B, Matrix.mul_apply, Fin.sum_univ_succ, hrow, Matrix.one_apply] using h
  have hdB : B.det = 1 := by
    rw [← fixScalar_det, ← hNB]
    simp [N, Matrix.det_mul, so4OfSU2xSU2_det_one, hd]
  obtain ⟨R, hR⟩ := so4_stabilizer B hB hdB
  refine ⟨P * R, R, ?_⟩
  rw [show R = 1 * R by simp, so4OfSU2xSU2_mul]
  simp only [one_mul]
  rw [hR, ← hNB]
  change _ * (so4OfSU2xSU2 P⁻¹ 1 * M) = _
  rw [← Matrix.mul_assoc, ← so4OfSU2xSU2_mul, mul_inv_cancel, mul_one, so4OfSU2xSU2_one, one_mul]

/-- Every oriented orthogonal transformation of the quaternion coordinates
is realized by a pair of determinant-one unitary matrices. -/
theorem so4CoverHom_surjective : Function.Surjective so4CoverHom := by
  intro A
  have hA := mem_specialOrthogonalGroup_iff.mp A.property
  obtain ⟨L, R, h⟩ := so4_surjective (A : R4)
    ((mem_orthogonalGroup_iff' (Fin 4) ℝ).mp hA.1) hA.2
  exact ⟨(L, R), Subtype.ext h⟩

end OmegaMath.SU2xSU2SO4Cover
