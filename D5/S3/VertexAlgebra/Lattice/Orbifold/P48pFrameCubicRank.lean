/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFrameCubicRank
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pFrameCubicRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three explicit cubic frame actions of P48p have fixed rank sixteen. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
import Mathlib.Tactic.Module
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
The signed row action `A = -t * u` commutes with the skew generator `J`.
The traces of `A`, `A ^ 2`, `A * J`, and `A ^ 2 * J` are computed from
one signed entry per row. Together with `J ^ 2 = -27 I` these traces give
fixed rank sixteen for `A`, `A * C`, and `A * C ^ 2`, with `C = (J - 3 I) / 6`.
Applying this result to pure cubics of the full lattice group requires a
separate identification with these frame actions up to conjugation.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameCubicRank

open scoped Matrix
open P48pSymmetricCommutantCertificate (signedFrameMatrix tFrameMatrix uFrameMatrix J JRat J_sq_rat)

open private tIndex tSign uIndex uSign ratCast from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate
open private sumOfFn_eq orderThree_fixedRank_eq_trace_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate

private abbrev FrameMatrix (R : Type*) := Matrix (Fin 48) (Fin 48) R

/-- The signed product in the catalogue's row convention. -/
def A : Matrix (Fin 48) (Fin 48) ℤ := -tFrameMatrix * uFrameMatrix

private def aIndex (i : Fin 48) : Fin 48 := uIndex (tIndex i)
private def aSign (i : Fin 48) : ℤ := -tSign i * uSign (tIndex i)
private def aIndex2 (i : Fin 48) : Fin 48 := aIndex (aIndex i)
private def aSign2 (i : Fin 48) : ℤ := aSign i * aSign (aIndex i)

private theorem signed_mul_apply (p : Fin 48 → Fin 48) (s : Fin 48 → ℤ)
    (B : FrameMatrix ℤ) (i j : Fin 48) :
    (signedFrameMatrix p s * B) i j = s i * B (p i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (p i) (Finset.mem_univ _)]
  · simp [signedFrameMatrix]
  · intro k _ hk
    simp [signedFrameMatrix, Ne.symm hk]

private theorem signed_mul (p q : Fin 48 → Fin 48) (s t : Fin 48 → ℤ) :
    signedFrameMatrix p s * signedFrameMatrix q t =
      signedFrameMatrix (fun i => q (p i)) (fun i => s i * t (p i)) := by
  apply Matrix.ext
  intro i j
  rw [signed_mul_apply]
  by_cases h : q (p i) = j <;> simp [signedFrameMatrix, h]

private theorem A_eq_signed : A = signedFrameMatrix aIndex aSign := by
  rw [A, neg_mul, tFrameMatrix, uFrameMatrix, signed_mul]
  apply Matrix.ext
  intro i j
  change -(if aIndex i = j then tSign i * uSign (tIndex i) else 0) =
    (if aIndex i = j then aSign i else 0)
  by_cases h : aIndex i = j <;> simp [h, aSign, neg_mul]

private theorem A_sq_eq_signed : A ^ 2 = signedFrameMatrix aIndex2 aSign2 := by
  rw [pow_two, A_eq_signed, signed_mul]

private theorem aIndex_cube (i : Fin 48) : aIndex (aIndex2 i) = i := by
  fin_cases i <;> decide +kernel

private theorem aSign_cube (i : Fin 48) : aSign2 i * aSign (aIndex2 i) = 1 := by
  fin_cases i <;> decide +kernel

private theorem A_cube : A ^ 3 = 1 := by
  rw [pow_succ, A_sq_eq_signed, A_eq_signed, signed_mul]
  apply Matrix.ext
  intro i j
  change (if aIndex (aIndex2 i) = j then aSign2 i * aSign (aIndex2 i) else 0) =
    (1 : FrameMatrix ℤ) i j
  rw [aIndex_cube, aSign_cube, Matrix.one_apply]

private theorem a_preserves_J (i : Fin 48) :
    ∀ j : Fin 48, aSign i * J (aIndex i) (aIndex j) = J i j * aSign j := by
  fin_cases i <;> decide +kernel

private theorem A_commute_J : Commute A J := by
  have hLeftInv : Function.LeftInverse aIndex2 aIndex := aIndex_cube
  have hSurj : Function.Surjective aIndex := fun j => ⟨aIndex2 j, aIndex_cube j⟩
  change A * J = J * A
  rw [A_eq_signed]
  apply Matrix.ext
  intro i k
  obtain ⟨j, rfl⟩ := hSurj k
  rw [signed_mul_apply, Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · simpa [signedFrameMatrix] using a_preserves_J i j
  · intro l _ hl
    have h : aIndex l ≠ aIndex j := fun he => hl (hLeftInv.injective he)
    simp [signedFrameMatrix, h]

private theorem trace_A : A.trace = 0 := by
  rw [A_eq_signed, Matrix.trace, ← sumOfFn_eq]
  decide +kernel

private theorem trace_A_sq : (A ^ 2).trace = 0 := by
  rw [A_sq_eq_signed, Matrix.trace, ← sumOfFn_eq]
  decide +kernel

private theorem trace_A_mul_J : (A * J).trace = 0 := by
  rw [A_eq_signed, Matrix.trace]
  simp only [Matrix.diag_apply, signed_mul_apply]
  rw [← sumOfFn_eq]
  decide +kernel

private theorem trace_A_sq_mul_J : (A ^ 2 * J).trace = 0 := by
  rw [A_sq_eq_signed, Matrix.trace]
  simp only [Matrix.diag_apply, signed_mul_apply]
  rw [← sumOfFn_eq]
  decide +kernel

/-- The rational form of the signed product. -/
def ARat : Matrix (Fin 48) (Fin 48) ℚ := ratCast A

/-- The normalized skew generator `Z1 / 12` in row coordinates. -/
def C : Matrix (Fin 48) (Fin 48) ℚ := (1 / 6 : ℚ) • (JRat - (3 : ℚ) • 1)

private theorem C_sq : C ^ 2 = (1 / 6 : ℚ) • (-JRat - (3 : ℚ) • 1) := by
  rw [pow_two, C]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_mul, mul_sub,
    J_sq_rat, mul_one, one_mul, smul_sub]
  module

private theorem C_cube : C ^ 3 = 1 := by
  rw [pow_succ, C_sq, C]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_mul, mul_sub,
    neg_mul, J_sq_rat, mul_one, one_mul, smul_sub, smul_neg]
  module

private theorem ARat_commute_C : Commute ARat C := by
  have h : ARat * JRat = JRat * ARat := by
    simpa only [map_mul, ARat, JRat] using congrArg ratCast A_commute_J.eq
  show ARat * C = C * ARat
  simp only [C, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one, one_mul, h]

private theorem trace_ratCast_of_zero (M : FrameMatrix ℤ) (h : M.trace = 0) :
    (ratCast M).trace = 0 := by
  change (M.map (Int.castRingHom ℚ)).trace = 0
  rw [← AddMonoidHom.map_trace (Int.castRingHom ℚ), h, map_zero]

private theorem trace_mul_C (B : FrameMatrix ℚ) (hB : B.trace = 0)
    (hBJ : (B * JRat).trace = 0) :
    (B * C).trace = 0 ∧ (B * C ^ 2).trace = 0 := by
  constructor
  · simp [C, Matrix.mul_smul, mul_sub, hB, hBJ]
  · simp [C_sq, Matrix.mul_smul, mul_sub, mul_neg, hB, hBJ]

/-- The column-coordinate realization of `x ↦ xM` after extending scalars. -/
noncomputable def rowAction (K : Type*) [Field K] [CharZero K]
    (M : Matrix (Fin 48) (Fin 48) ℚ) : Module.End K (Fin 48 → K) :=
  ((Mᵀ).map (Rat.castHom K)).toLin'

private theorem rowAction_cube_and_fixedRank16 (K : Type*) [Field K] [CharZero K]
    (M : FrameMatrix ℚ) (hCube : M ^ 3 = 1)
    (hTrace : M.trace = 0) (hTraceSquare : (M ^ 2).trace = 0) :
    (rowAction K M) ^ 3 = 1 ∧ Module.finrank K (LinearMap.ker (rowAction K M - 1)) = 16 := by
  have hTransCube : (Mᵀ) ^ 3 = 1 := by
    rw [← Matrix.transpose_pow, hCube, Matrix.transpose_one]
  have hActionCube : (rowAction K M) ^ 3 = 1 := by
    change (((Rat.castHom K).mapMatrix (Mᵀ)).toLin') ^ 3 = 1
    rw [← Matrix.toLin'_pow, ← map_pow, hTransCube, map_one, Matrix.toLin'_one,
      ← Module.End.one_eq_id]
  have hActionTrace : LinearMap.trace K (Fin 48 → K) (rowAction K M) = 0 := by
    rw [rowAction, Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace (Rat.castHom K),
      Matrix.trace_transpose, hTrace, map_zero]
  have hActionTraceSquare : LinearMap.trace K (Fin 48 → K) ((rowAction K M) ^ 2) = 0 := by
    rw [rowAction, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, ← Matrix.map_pow,
      ← AddMonoidHom.map_trace (Rat.castHom K), ← Matrix.transpose_pow,
      Matrix.trace_transpose, hTraceSquare, map_zero]
  refine ⟨hActionCube, (Nat.cast_inj (R := K)).mp ?_⟩
  have hDim : Module.finrank K (Fin 48 → K) = 48 := by simp [Module.finrank_pi]
  rw [orderThree_fixedRank_eq_trace_sum (rowAction K M) hActionCube,
    hDim, hActionTrace, hActionTraceSquare]
  norm_num

/-- Each of the three explicit frame actions cubes to the identity and has
a sixteen-dimensional fixed space over any characteristic-zero field. -/
theorem frame_cubic_cube_and_fixedRank16 (K : Type*) [Field K] [CharZero K]
    (M : Matrix (Fin 48) (Fin 48) ℚ) (hM : M ∈ ({ARat, ARat * C, ARat * C ^ 2} : Set _)) :
    (rowAction K M) ^ 3 = 1 ∧ Module.finrank K (LinearMap.ker (rowAction K M - 1)) = 16 := by
  have hA : ARat ^ 3 = 1 := by
    rw [ARat, ← map_pow, A_cube, map_one]
  have hA0 : ARat.trace = 0 := trace_ratCast_of_zero A trace_A
  have hA20 : (ARat ^ 2).trace = 0 := by
    simpa only [map_pow, ARat] using trace_ratCast_of_zero (A ^ 2) trace_A_sq
  have hAJ0 : (ARat * JRat).trace = 0 := by
    simpa only [map_mul, ARat, JRat] using trace_ratCast_of_zero (A * J) trace_A_mul_J
  have hA2J0 : (ARat ^ 2 * JRat).trace = 0 := by
    simpa only [map_mul, map_pow, ARat, JRat] using
      trace_ratCast_of_zero (A ^ 2 * J) trace_A_sq_mul_J
  have hComm := ARat_commute_C
  have hComm2 := hComm.pow_right 2
  have hC4 : (C ^ 2) ^ 2 = C := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_succ, C_cube, one_mul]
  obtain ⟨hAC0, hAC20⟩ := trace_mul_C ARat hA0 hAJ0
  obtain ⟨hA2C0, hA2C20⟩ := trace_mul_C (ARat ^ 2) hA20 hA2J0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl
  · exact rowAction_cube_and_fixedRank16 K ARat hA hA0 hA20
  · refine rowAction_cube_and_fixedRank16 K (ARat * C) ?_ hAC0 ?_
    · rw [hComm.mul_pow, hA, C_cube, one_mul]
    · rw [hComm.mul_pow, hA2C20]
  · refine rowAction_cube_and_fixedRank16 K (ARat * C ^ 2) ?_ hAC20 ?_
    · rw [hComm2.mul_pow, pow_right_comm C 2 3, hA, C_cube, one_pow, one_mul]
    · rw [hComm2.mul_pow, hC4, hA2C0]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameCubicRank
