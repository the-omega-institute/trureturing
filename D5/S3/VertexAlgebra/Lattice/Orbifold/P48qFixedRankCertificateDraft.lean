/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificateDraft
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedChargeAction.g_cube; instance=D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificateDraft.nebeOrderThree; result=D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificateDraft.nebeOrderThree_cube
   digest: Exact cube and trace checks for the Nebe matrix and their fixed-rank consequence. -/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# P48q fixed rank certificate (source draft)

Nebe's lattice data at
https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/P48q.html
is recorded in `p48q-order-three-certificate.json` in this recovery directory.
The saved HTML SHA-256 is
c1f04856618da946626600a588ebc14ebdb2683fe86786ff3b4828ac1ed10616.
The matrix below is the fourth power of the first listed generator, in
Nebe's row-vector convention. The JSON also contains the Gram matrix in
that basis. Its isometry equation is A G Aᵀ = G. The fixed-rank calculation
uses the transpose of A to act on column coordinates.

The square table is computed with exact integer arithmetic from the saved
matrix. List dot products are checked by kernel reduction and proved to
agree with Mathlib matrix multiplication. The link from this concrete matrix
to the abstract group action is an external identification.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace P48qFixedRankCertificateDraft

open scoped Matrix

section General

variable {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Averaging the powers of an endomorphism with cube equal to the identity
gives a projection onto its fixed subspace. -/
theorem orderThreeAverage_isProj (A : Module.End K V) (hA : A ^ 3 = 1) :
    LinearMap.IsProj (LinearMap.ker (A - 1))
      ((3 : K)⁻¹ • (1 + A + A ^ 2)) := by
  let P : Module.End K V := (3 : K)⁻¹ • (1 + A + A ^ 2)
  have hcube (x : V) : A (A (A x)) = x := by
    have h := congrArg (fun f : Module.End K V => f x) hA
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      Module.End.one_apply] using h
  change LinearMap.IsProj (LinearMap.ker (A - 1)) P
  constructor
  · intro x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    simp only [P, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, pow_two, Module.End.mul_apply,
      map_smul, map_add, hcube]
    congr 1 <;> abel
  · intro x hx
    have hfix : A x = x := by
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, sub_eq_zero] using hx
    have hsum : x + x + x = (3 : K) • x := by
      rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    calc
      P x = (3 : K)⁻¹ • (x + x + x) := by
        simp only [P, LinearMap.smul_apply, LinearMap.add_apply,
          Module.End.one_apply, pow_two, Module.End.mul_apply, hfix]
      _ = (3 : K)⁻¹ • ((3 : K) • x) := by rw [hsum]
      _ = x := by rw [smul_smul, inv_mul_cancel₀ (by norm_num : (3 : K) ≠ 0), one_smul]

/-- The fixed rank, viewed in the coefficient field, is the trace of
the averaging projection. -/
theorem orderThree_fixedRank_eq_trace (A : Module.End K V) (hA : A ^ 3 = 1) :
    (Module.finrank K (LinearMap.ker (A - 1)) : K) =
      LinearMap.trace K V ((3 : K)⁻¹ • (1 + A + A ^ 2)) := by
  exact (orderThreeAverage_isProj A hA).trace.symm

/-- Expand the trace using its linearity and the trace of the identity. -/
theorem orderThree_fixedRank_eq_trace_sum (A : Module.End K V) (hA : A ^ 3 = 1) :
    (Module.finrank K (LinearMap.ker (A - 1)) : K) =
      (3 : K)⁻¹ * ((Module.finrank K V : K) +
        LinearMap.trace K V A + LinearMap.trace K V (A ^ 2)) := by
  rw [orderThree_fixedRank_eq_trace A hA]
  simp only [map_smul, map_add, LinearMap.trace_one, smul_eq_mul]

end General

/-- The real or rational column-coordinate realization of a row-action
integer matrix in Nebe's convention. -/
noncomputable def rowAction (K : Type*) [Field K] (A : Matrix (Fin 48) (Fin 48) ℤ) :
    Module.End K (Fin 48 → K) :=
  ((Aᵀ).map (Int.castRingHom K)).toLin'

/-- All three integer certificate inputs are explicit. Transposition and
extension of scalars preserve the two traces and the cube relation. -/
theorem rowAction_fixedRank16_of_certificate
    (K : Type*) [Field K] [CharZero K]
    (M : Matrix (Fin 48) (Fin 48) ℤ) (hCube : M ^ 3 = 1)
    (hTrace : M.trace = 0) (hTraceSquare : (M ^ 2).trace = 0) :
    Module.finrank K (LinearMap.ker (rowAction K M - 1)) = 16 := by
  let N : Matrix (Fin 48) (Fin 48) K := (Mᵀ).map (Int.castRingHom K)
  have hTransCube : (Mᵀ) ^ 3 = 1 := by
    rw [← Matrix.transpose_pow, hCube, Matrix.transpose_one]
  have hTransTraceSquare : ((Mᵀ) ^ 2).trace = 0 := by
    rw [← Matrix.transpose_pow, Matrix.trace_transpose, hTraceSquare]
  have hNCube : N ^ 3 = 1 := by
    change ((Int.castRingHom K).mapMatrix (Mᵀ)) ^ 3 = 1
    rw [← map_pow, hTransCube, map_one]
  have hNTrace : N.trace = 0 := by
    change ((Mᵀ).map (Int.castRingHom K)).trace = 0
    rw [← AddMonoidHom.map_trace (Int.castRingHom K),
      Matrix.trace_transpose, hTrace, map_zero]
  have hNTraceSquare : (N ^ 2).trace = 0 := by
    change (((Mᵀ).map (Int.castRingHom K)) ^ 2).trace = 0
    rw [← Matrix.map_pow, ← AddMonoidHom.map_trace (Int.castRingHom K),
      hTransTraceSquare, map_zero]
  have hActionCube : (rowAction K M) ^ 3 = 1 := by
    change N.toLin' ^ 3 = 1
    rw [← Matrix.toLin'_pow, hNCube, Matrix.toLin'_one, ← Module.End.one_eq_id]
  have hActionTrace : LinearMap.trace K (Fin 48 → K) (rowAction K M) = 0 := by
    change LinearMap.trace K (Fin 48 → K) N.toLin' = 0
    rw [Matrix.trace_toLin'_eq, hNTrace]
  have hActionTraceSquare :
      LinearMap.trace K (Fin 48 → K) ((rowAction K M) ^ 2) = 0 := by
    change LinearMap.trace K (Fin 48 → K) (N.toLin' ^ 2) = 0
    rw [← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, hNTraceSquare]
  have hDim : Module.finrank K (Fin 48 → K) = 48 := by
    simp [Module.finrank_pi]
  apply (Nat.cast_inj (R := K)).mp
  rw [orderThree_fixedRank_eq_trace_sum (rowAction K M) hActionCube,
    hDim, hActionTrace, hActionTraceSquare]
  norm_num

private def nebeOrderThreeDataRow0 : Array ℤ := #[-6, 2, -7, 2, 6, 3, -7, -1, -8, 4, -4, -3, -6, -5, 4, 0, 0, -2, 2, 1, -1, -1, 0, 3, 1, 1, -1, -1, 2, -1, -2, -2, 2, 0, 0, -2, 1, 2, 0, 2, 0, -1, 0, 0, 1, -1, 0, 1]
private def nebeOrderThreeDataRow1 : Array ℤ := #[-1, 0, -1, 1, 3, 1, -5, 0, -5, 2, -3, -2, -5, -2, 3, 1, 1, -2, 1, -1, 0, -2, 1, 2, 2, 0, -1, 1, 0, -1, -1, -1, 3, 0, 1, -1, 1, 1, 1, 1, 0, -1, 0, -1, 1, -1, 1, 0]
private def nebeOrderThreeDataRow2 : Array ℤ := #[-19, 3, -6, 12, 7, 8, -16, -7, -14, 5, -7, -4, -10, -5, 5, -1, -2, -5, 4, 4, -2, -3, -1, 3, 1, -1, -3, -1, 4, -1, -3, 1, -1, -4, 1, -3, 2, 3, -2, 0, 2, -1, 2, 2, 0, 0, -2, 1]
private def nebeOrderThreeDataRow3 : Array ℤ := #[6, 4, -9, -6, 3, -3, 10, 6, 4, 0, 4, -1, 7, -2, 0, 0, 2, 2, -1, 3, 0, 5, -1, 0, -3, 4, 0, 0, 0, 0, -2, -3, 0, 3, -3, 0, -1, -1, 1, 2, -1, -1, 0, 0, 0, 0, 0, 0]
private def nebeOrderThreeDataRow4 : Array ℤ := #[-8, -3, 0, 8, 0, 6, -10, -7, -5, 0, -7, -1, -7, -3, 2, -2, -4, -2, 2, 0, -4, -3, -2, 0, 3, -4, 1, -3, 2, 0, 2, 3, 1, -2, 1, 0, 2, 2, -2, 0, 0, 1, 1, -1, 2, -1, -1, 1]
private def nebeOrderThreeDataRow5 : Array ℤ := #[-4, 2, 1, 0, 2, 0, -5, -1, -7, 4, -1, -1, -6, -2, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, -1, -2, 1, 1, 0, -1, -1, 1, 0, 2, -1, 1, 1, 1, 0, 1, -1, 0, 0, 0, 0, 1, 0]
private def nebeOrderThreeDataRow6 : Array ℤ := #[-12, 2, -10, 8, 5, 8, -6, -3, -7, 2, -5, -3, -3, -5, 3, -1, -3, -2, 3, 6, -3, 0, -3, 1, -2, 1, -1, -3, 4, 0, -2, 1, -1, -2, -1, -2, 2, 2, -2, 0, 1, -1, 3, 1, 1, 0, -3, 1]
private def nebeOrderThreeDataRow7 : Array ℤ := #[5, 0, 5, -4, -1, -5, 6, 3, 6, -2, 4, 4, 4, 4, -3, 1, 2, 1, -2, -2, 3, 1, 2, 0, -2, 1, 0, 1, -1, 0, 0, -1, -2, 2, 0, 1, -1, -2, 1, -2, 0, 1, -1, 1, -2, 2, 1, 0]
private def nebeOrderThreeDataRow8 : Array ℤ := #[4, 2, -2, -3, 0, -2, 5, 3, 2, 0, 2, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 1, 0, 0, -1, 1, -1, 1, 0, 0, -1, -1, 1, 1, 0, 0, 0, -1, 1, 0, 0, -1, 1, -1, 1, 0, 1, -1]
private def nebeOrderThreeDataRow9 : Array ℤ := #[-9, 5, -12, 4, 11, 4, -9, -2, -11, 7, -7, -4, -11, -8, 7, 2, -1, -5, 2, 6, -2, -2, -1, 4, -1, 1, -3, -3, 5, 0, -3, -1, 1, 0, 1, -4, 3, 2, -1, 0, 1, -2, 2, 0, 2, 0, -1, 0]
private def nebeOrderThreeDataRow10 : Array ℤ := #[13, -2, 13, -11, -12, -10, 13, 3, 13, -3, 10, 4, 9, 8, -7, 0, 2, 6, -4, -6, 2, 2, 1, -5, 1, -3, 3, 1, -4, 2, 4, 1, -2, 1, -1, 5, -3, -2, 0, -1, -1, 2, -3, -2, -1, 0, 2, -1]
private def nebeOrderThreeDataRow11 : Array ℤ := #[11, -4, 10, -5, -6, -5, 6, 0, 9, -4, 2, 4, 2, 5, -3, 0, -1, 3, -4, -4, 1, 0, 1, -3, 1, -3, 3, 0, -3, 1, 4, 2, -1, 1, 1, 3, -1, -1, 0, -2, -1, 2, -2, -1, -1, 1, 1, 0]
private def nebeOrderThreeDataRow12 : Array ℤ := #[-1, -3, -1, 6, 2, 5, -8, -3, -4, -1, -7, -1, -6, -2, 3, 0, -2, -3, 1, 0, -2, -3, 0, 2, 2, -1, 0, 0, 1, -2, 0, 1, 3, -1, 2, -2, 2, 1, 0, 1, -1, 0, 1, 0, 1, -1, 0, 0]
private def nebeOrderThreeDataRow13 : Array ℤ := #[-4, -1, 0, -1, 2, 0, -8, -3, -7, 6, -3, -2, -9, -3, 3, 0, 0, -1, 0, -1, 1, -4, 1, 2, 2, -1, -1, -1, 1, 0, 1, 0, 1, 0, 1, -1, 1, 2, -1, 0, 1, 0, -1, 0, 1, -1, 0, 0]
private def nebeOrderThreeDataRow14 : Array ℤ := #[-2, 4, 6, -4, -3, -6, 1, 0, -1, 5, 6, 0, -1, 3, -1, 2, 2, 1, -1, -2, 3, -2, 2, 0, 0, -1, -2, 2, 0, 1, 0, 0, -3, -1, 1, 0, -1, 0, 0, -1, 1, 0, -1, 1, -2, 1, 1, -2]
private def nebeOrderThreeDataRow15 : Array ℤ := #[20, -2, 9, -10, -8, -9, 16, 4, 16, -6, 7, 4, 10, 6, -5, 0, 1, 3, -6, -1, 1, 4, -1, -5, 0, -1, 3, 1, -4, 3, 4, 2, -1, 3, -1, 3, -2, -4, 1, -1, -1, 1, -2, -1, -1, 1, 2, -2]
private def nebeOrderThreeDataRow16 : Array ℤ := #[0, 3, 4, -5, -2, -5, 3, 1, 1, 3, 6, 0, 2, 1, -2, 0, 2, 1, -1, -1, 2, 1, 0, -1, 1, 0, 0, 0, -1, 3, 1, 0, -2, 1, -1, 1, -2, -1, 0, 0, 1, 0, -2, 0, -1, 0, 1, -1]
private def nebeOrderThreeDataRow17 : Array ℤ := #[2, 2, 0, -3, -2, -3, 4, 1, 2, 0, 4, 0, 3, 1, -1, 0, 0, 2, -1, -1, 0, 2, 0, -1, 0, 0, 0, 1, -1, 0, 0, -1, -1, 0, -1, 1, -1, 0, 1, 1, 0, 0, -1, 0, -1, 0, 0, 0]
private def nebeOrderThreeDataRow18 : Array ℤ := #[-8, 0, -4, 2, 3, 4, -10, -5, -7, 6, -4, -3, -10, -3, 4, 1, -2, -3, 1, 4, -1, -3, -1, 2, 0, 0, -1, -3, 3, 1, 0, 1, 0, -2, 0, -2, 1, 3, -2, -1, 2, -1, 0, 0, 1, -1, -1, 0]
private def nebeOrderThreeDataRow19 : Array ℤ := #[4, -4, 7, 0, -4, 0, -1, -1, 2, -2, 0, 1, 0, 4, -2, 0, 0, 1, -2, -2, 2, -1, 1, -1, 1, -1, 1, 2, -2, -1, 1, 2, 0, -1, 1, 1, 0, 0, 0, -1, 0, 1, -1, 1, -1, 0, 0, 0]
private def nebeOrderThreeDataRow20 : Array ℤ := #[0, 1, -7, 0, 2, 2, 1, 3, -2, 1, 0, -2, 2, -2, 2, 0, 1, 1, 2, 0, 0, 1, 0, 2, -1, 3, -1, 2, 0, -2, -2, -2, 2, 1, -1, -1, 0, 1, 1, 2, -1, -1, 1, 0, 0, -1, 0, 0]
private def nebeOrderThreeDataRow21 : Array ℤ := #[-1, 4, 5, -4, -2, -6, 2, 0, 1, 4, 6, 1, 1, 3, -1, 1, 2, 0, -1, 0, 3, 0, 1, 0, -1, 0, -2, 2, -1, 2, 0, 0, -3, 0, 0, 0, -2, -1, 0, -2, 2, 0, -1, 1, -2, 1, 1, -2]
private def nebeOrderThreeDataRow22 : Array ℤ := #[4, -2, 3, -2, -2, 0, -1, 0, 0, 0, 0, 1, -2, 2, 0, 3, 0, -1, 0, -2, 1, -2, 2, 2, 0, 1, -1, 2, -1, -1, 0, -1, 2, 0, 2, -1, 0, 0, 2, 0, 0, 0, 0, 0, 0, -1, 1, -1]
private def nebeOrderThreeDataRow23 : Array ℤ := #[-4, 0, 4, 3, -1, 1, -6, -3, -4, 2, -2, -1, -5, 1, 1, 0, -1, -1, 0, -1, 0, -2, 0, 0, 2, -3, 0, 0, 1, 0, 0, 2, 0, -2, 1, 0, 1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0]
private def nebeOrderThreeDataRow24 : Array ℤ := #[1, -3, 2, 1, -1, 2, -2, -1, -1, -1, -2, 1, -2, 0, 0, 1, -1, -1, 0, -1, 0, -2, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, -1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
private def nebeOrderThreeDataRow25 : Array ℤ := #[-13, 6, -8, 6, 7, 3, -8, -2, -10, 5, -4, -3, -6, -5, 5, 1, -1, -3, 4, 3, -2, -3, 0, 3, -1, 1, -3, -1, 3, -1, -3, -2, 0, -2, 1, -3, 2, 2, 0, 1, 1, -1, 2, 0, 1, 0, -1, 0]
private def nebeOrderThreeDataRow26 : Array ℤ := #[-3, 0, 6, -2, -4, -2, -2, -4, 1, 3, 3, 0, -2, 2, -2, 0, -2, 0, -1, 0, 0, -1, -1, -2, 1, -3, 1, -3, 1, 4, 3, 3, -3, -1, 0, 1, -1, 0, -2, -2, 1, 1, -2, -1, 0, 0, 0, -1]
private def nebeOrderThreeDataRow27 : Array ℤ := #[0, -2, 6, 1, -1, -1, -3, -3, 0, -1, -2, 1, -3, 1, -1, 0, -1, -1, -1, -2, 0, -2, 0, -1, 2, -3, 1, -1, 0, 1, 2, 2, 0, 0, 2, 1, 1, -1, 0, -1, 0, 1, -1, -1, 1, 1, 1, 0]
private def nebeOrderThreeDataRow28 : Array ℤ := #[-26, 2, -12, 16, 12, 13, -23, -8, -19, 6, -11, -5, -13, -9, 7, -1, -3, -7, 7, 4, -3, -5, -1, 7, 1, 2, -3, -3, 6, -2, -4, -1, 1, -3, 1, -5, 3, 4, -1, 2, 1, -1, 2, 2, 1, -1, -2, 2]
private def nebeOrderThreeDataRow29 : Array ℤ := #[12, 1, 3, -9, -4, -7, 11, 7, 6, -2, 5, 2, 7, 4, -3, 1, 4, 6, -2, -6, 3, 1, 4, -1, -1, 1, 1, 4, -3, -3, -1, -3, 1, 2, 0, 2, -1, -1, 2, 2, -2, 1, -1, 0, -1, 0, 2, 0]
private def nebeOrderThreeDataRow30 : Array ℤ := #[2, -1, 5, -1, 0, -2, -4, -1, -2, 2, -1, -1, -5, 0, 1, 1, 1, -2, -1, -2, 1, -3, 1, 1, 3, -1, 0, 1, -1, 0, 1, 1, 2, 1, 1, 0, 1, 0, 1, 0, 0, 0, -1, -1, 1, -1, 2, -1]
private def nebeOrderThreeDataRow31 : Array ℤ := #[-5, 1, 0, 4, 0, 1, -4, -4, 0, 1, -3, 1, -4, 0, 2, 0, -3, -1, 1, 2, -3, -2, -1, 0, -1, -2, 0, -3, 2, 1, 1, 2, -2, -2, 0, 0, 1, 1, -2, -2, 1, 1, 1, -1, 0, 0, -1, 0]
private def nebeOrderThreeDataRow32 : Array ℤ := #[12, -3, 4, -4, -7, -3, 11, 4, 12, -6, 4, 2, 9, 5, -4, 0, 0, 4, -2, -1, -1, 2, 0, -4, -1, 0, 3, 0, -3, 0, 2, 1, 0, 0, -2, 3, -1, -1, 0, 0, -2, 1, 0, -2, 0, -1, 0, -1]
private def nebeOrderThreeDataRow33 : Array ℤ := #[3, -2, 2, -3, 0, -2, -1, -1, 0, 1, 1, 0, -1, 0, 0, -1, 1, -1, -2, 0, 2, 1, 0, 0, 1, 0, -1, 1, -1, 1, 1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 0, -2, 1, -1, 0, 0, 0]
private def nebeOrderThreeDataRow34 : Array ℤ := #[0, 0, 1, 1, -1, 0, 0, 0, 1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 1, 0, -1, -1, 0, 1, 1, 0, 0, 0, 0, 0]
private def nebeOrderThreeDataRow35 : Array ℤ := #[2, -2, 2, 2, 3, 1, -5, 0, -3, 0, -5, 0, -6, -1, 3, 1, 0, -2, 0, -3, 1, -3, 2, 2, 2, -1, 0, 1, 0, -2, 0, 0, 3, 1, 2, -1, 2, 1, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0]
private def nebeOrderThreeDataRow36 : Array ℤ := #[21, -1, 14, -15, -14, -12, 17, 6, 14, -3, 11, 4, 9, 10, -6, 3, 3, 7, -5, -7, 4, 1, 3, -5, 0, -2, 2, 5, -6, 0, 3, 0, 0, 1, 1, 4, -3, -2, 2, -1, -1, 1, -2, -2, -1, 0, 3, -3]
private def nebeOrderThreeDataRow37 : Array ℤ := #[4, -3, 0, 2, -1, 1, 2, 1, 4, -5, -1, 2, 5, 1, -1, -3, 1, 1, 0, -1, 0, 2, 0, 0, 0, 1, 1, 2, -2, -2, 0, 0, 1, 1, -1, 1, -1, -1, 0, 1, -1, 1, 0, 1, -1, 0, 0, 1]
private def nebeOrderThreeDataRow38 : Array ℤ := #[-22, 6, -15, 10, 14, 8, -16, -3, -17, 8, -6, -5, -10, -9, 7, 0, -1, -5, 6, 4, -1, -2, 0, 7, -1, 4, -4, -2, 5, -1, -5, -3, 0, -1, 0, -5, 1, 3, 0, 2, 1, -2, 1, 2, 0, 0, -2, 1]
private def nebeOrderThreeDataRow39 : Array ℤ := #[-1, 0, 2, 1, -2, 1, -2, -2, -2, 1, -2, 0, -2, 0, 0, -1, 1, 1, 0, 0, 0, -1, 0, -1, 1, -2, 0, 1, 0, -1, 0, 2, -1, -1, 0, 1, 1, 1, -2, -1, 1, 1, 1, 1, 0, -1, 0, 1]
private def nebeOrderThreeDataRow40 : Array ℤ := #[-5, 0, -7, 3, 2, 5, -1, -1, -1, -1, -1, 0, 2, -4, 0, -1, -2, -2, 3, 3, -3, 2, -3, 1, -1, 2, 0, -3, 2, 1, 0, -1, 0, 1, -2, -1, 0, 0, 0, 1, 0, 0, 1, 0, 1, -1, -1, 1]
private def nebeOrderThreeDataRow41 : Array ℤ := #[4, 3, 10, -7, -6, -9, 11, 5, 8, -1, 11, 4, 11, 6, -7, 1, 4, 3, -1, -4, 4, 2, 1, -2, -1, 1, 0, 2, -3, 3, 1, -1, -3, 2, 0, 2, -3, -4, 2, -1, 0, 1, -2, 0, -2, 2, 2, -2]
private def nebeOrderThreeDataRow42 : Array ℤ := #[-8, -1, 3, 3, 0, 1, -8, -3, -7, 3, -1, -1, -4, -1, 0, -2, 1, 0, 2, -4, 1, -3, 2, 1, 3, -2, -1, 1, 0, -1, 0, 0, 0, -1, 1, 0, 0, 1, -1, 1, 0, 1, -1, 1, 0, -1, 0, 1]
private def nebeOrderThreeDataRow43 : Array ℤ := #[13, -1, 5, -7, -2, -7, 8, 4, 9, -2, 3, 2, 2, 4, -1, 2, 2, 1, -4, -1, 2, 0, 2, -1, -1, 0, 1, 1, -2, 0, 1, 0, 1, 2, 0, 1, -1, -2, 1, -1, -1, 0, -1, -1, 0, 1, 2, -2]
private def nebeOrderThreeDataRow44 : Array ℤ := #[-3, 3, 0, -2, 5, -4, -6, -1, -6, 6, -1, -1, -8, -2, 4, 2, 2, -3, 0, -1, 2, -3, 2, 4, 1, 0, -3, 1, 1, 0, -1, -2, 1, 1, 2, -2, 0, 0, 1, 0, 1, -1, -1, 0, 0, 1, 2, -1]
private def nebeOrderThreeDataRow45 : Array ℤ := #[7, 2, 5, -8, -2, -6, 4, 3, 1, 2, 5, 1, 0, 2, -1, 3, 3, 0, -2, -2, 3, 0, 2, 0, 1, 1, -1, 2, -2, 1, 0, -2, 0, 1, 1, 0, -1, -1, 2, 0, 1, -1, -2, 0, -1, 0, 2, -1]
private def nebeOrderThreeDataRow46 : Array ℤ := #[20, -4, 5, -10, -10, -6, 20, 8, 17, -9, 8, 5, 16, 7, -7, 0, 3, 7, -4, -3, 2, 5, 1, -4, -3, 2, 3, 4, -5, -2, 1, -1, 0, 3, -2, 4, -2, -3, 2, 0, -2, 1, 0, 0, -1, 0, 1, 0]
private def nebeOrderThreeDataRow47 : Array ℤ := #[0, 3, -7, -2, 4, -1, 0, 2, -3, 4, -2, -3, -3, -3, 3, 1, 2, 0, 0, 3, -1, -1, 0, 1, -1, 1, -1, -1, 2, -1, -2, -1, 1, 0, -1, -1, 2, 1, -1, 1, 0, -1, 1, -1, 2, -1, 0, 0]

private def nebeOrderThreeData : Array (Array ℤ) := #[
  nebeOrderThreeDataRow0, nebeOrderThreeDataRow1, nebeOrderThreeDataRow2, nebeOrderThreeDataRow3,
  nebeOrderThreeDataRow4, nebeOrderThreeDataRow5, nebeOrderThreeDataRow6, nebeOrderThreeDataRow7,
  nebeOrderThreeDataRow8, nebeOrderThreeDataRow9, nebeOrderThreeDataRow10, nebeOrderThreeDataRow11,
  nebeOrderThreeDataRow12, nebeOrderThreeDataRow13, nebeOrderThreeDataRow14, nebeOrderThreeDataRow15,
  nebeOrderThreeDataRow16, nebeOrderThreeDataRow17, nebeOrderThreeDataRow18, nebeOrderThreeDataRow19,
  nebeOrderThreeDataRow20, nebeOrderThreeDataRow21, nebeOrderThreeDataRow22, nebeOrderThreeDataRow23,
  nebeOrderThreeDataRow24, nebeOrderThreeDataRow25, nebeOrderThreeDataRow26, nebeOrderThreeDataRow27,
  nebeOrderThreeDataRow28, nebeOrderThreeDataRow29, nebeOrderThreeDataRow30, nebeOrderThreeDataRow31,
  nebeOrderThreeDataRow32, nebeOrderThreeDataRow33, nebeOrderThreeDataRow34, nebeOrderThreeDataRow35,
  nebeOrderThreeDataRow36, nebeOrderThreeDataRow37, nebeOrderThreeDataRow38, nebeOrderThreeDataRow39,
  nebeOrderThreeDataRow40, nebeOrderThreeDataRow41, nebeOrderThreeDataRow42, nebeOrderThreeDataRow43,
  nebeOrderThreeDataRow44, nebeOrderThreeDataRow45, nebeOrderThreeDataRow46, nebeOrderThreeDataRow47
]

/-- Exact integer row-action matrix from the persisted Nebe certificate. -/
def nebeOrderThree : Matrix (Fin 48) (Fin 48) ℤ :=
  fun i j => (nebeOrderThreeData.getD i.val #[]).getD j.val 0

private def nebeSquareDataRow0 : Array ℤ := #[2, -1, 6, -2, -6, -2, 3, 0, 3, 0, 2, 1, 3, 3, -3, -1, 2, 3, -1, -1, 1, 0, 0, -2, 1, -2, 1, 1, -1, 1, 1, 2, -1, -1, -1, 2, 0, 0, -2, -1, 1, 1, 0, 0, 0, -1, 0, 0]
private def nebeSquareDataRow1 : Array ℤ := #[-2, -3, 1, 1, -3, 2, 0, -1, 0, -1, 0, 1, 2, 0, -2, -2, 0, 2, 1, -2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 1, 0, 1, -1, 1, 0, 1, 0, 1, 0, -1, -1, 1]
private def nebeSquareDataRow2 : Array ℤ := #[11, -3, 7, -3, -6, -3, 9, 3, 8, -6, 3, 2, 8, 4, -4, -2, 2, 3, -3, -2, 1, 2, 0, -4, 1, -1, 3, 2, -4, 0, 2, 2, 0, 1, -1, 3, -1, -2, 0, 0, -1, 1, -1, 0, 0, 0, 1, 0]
private def nebeSquareDataRow3 : Array ℤ := #[-17, 4, -2, 9, 5, 4, -17, -6, -15, 9, -7, -5, -12, -4, 5, 0, 0, -3, 4, 2, 0, -6, 0, 3, 2, -3, -4, 0, 4, -1, -3, 2, 0, -4, 2, -3, 3, 2, -3, 0, 2, 0, 2, 1, 1, -1, -1, -1]
private def nebeSquareDataRow4 : Array ℤ := #[27, -3, 13, -15, -16, -11, 28, 10, 23, -11, 14, 6, 22, 11, -11, -1, 6, 10, -7, -4, 3, 8, 1, -9, -1, 0, 5, 5, -8, 1, 3, 1, -2, 2, -3, 7, -4, -4, 1, -1, -2, 1, -2, -1, -2, 0, 2, 0]
private def nebeSquareDataRow5 : Array ℤ := #[4, -5, 4, -1, -1, 0, 2, 0, 4, -4, 0, 4, 3, 1, -2, -3, 0, 0, -2, -3, 2, 2, 0, 0, 1, 0, 2, 0, -1, 1, 2, 0, 0, 3, -1, 1, -1, -1, 0, 0, 0, 1, -2, 2, -2, 1, 0, 2]
private def nebeSquareDataRow6 : Array ℤ := #[-10, 10, -10, 4, 7, 1, -6, 1, -12, 7, -2, -5, -5, -4, 6, 1, 1, 0, 3, 2, 0, -2, 2, 2, -2, 1, -4, 2, 3, -4, -6, -2, -2, -3, 0, -3, 2, 3, -1, 2, 0, -1, 2, 2, -2, 0, -1, 0]
private def nebeSquareDataRow7 : Array ℤ := #[-1, -2, 2, -2, 4, -2, -5, -3, 0, 2, 1, 1, -6, -1, 2, 2, -3, -6, -1, 0, 1, -1, -1, 3, 1, 1, -1, -3, 0, 4, 3, -1, 1, 3, 2, -2, -2, -2, 3, -1, 1, -1, -3, -1, 0, 2, 1, -2]
private def nebeSquareDataRow8 : Array ℤ := #[5, -4, 6, -5, -3, -3, 1, 0, 3, 0, 2, 2, 0, 2, -2, 0, 1, 1, -2, -3, 3, -1, 1, 0, 1, 0, 1, 0, -1, 1, 2, 0, 0, 2, 0, 1, -1, -1, 0, 0, 0, 1, -2, 1, -1, 0, 1, 0]
private def nebeSquareDataRow9 : Array ℤ := #[8, 1, 10, -5, -5, -7, 3, 1, 2, 1, 2, 2, 0, 5, -1, 1, 2, 3, -3, -5, 4, -2, 3, -1, 1, -3, 0, 4, -2, -1, 0, 1, 0, 0, 2, 1, 0, -1, 0, 0, 0, 2, -1, 1, -2, 1, 2, -1]
private def nebeSquareDataRow10 : Array ℤ := #[9, -7, 5, -4, -5, -1, 8, 1, 12, -6, 3, 4, 7, 3, -5, -2, 1, 1, -3, 1, 0, 4, -2, -3, 0, 0, 3, -2, -2, 3, 4, 2, -1, 2, -2, 3, -2, -2, -1, -3, 0, 0, -1, -1, 0, 0, 0, 1]
private def nebeSquareDataRow11 : Array ℤ := #[17, 0, 7, -10, -6, -9, 16, 5, 13, -5, 8, 4, 9, 5, -4, 1, 1, 3, -5, -3, 1, 5, 0, -4, 0, -1, 2, 2, -4, 2, 3, 0, 0, 3, 0, 3, -2, -3, 3, -1, -1, 0, -2, -2, -1, 2, 2, -1]
private def nebeSquareDataRow12 : Array ℤ := #[10, -1, 7, -4, -8, -3, 10, 3, 8, -5, 4, 2, 8, 6, -5, 0, 2, 5, -3, -2, 1, 2, 1, -4, 0, -1, 3, 3, -3, -1, 0, 1, 0, -1, 0, 3, -1, -1, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0]
private def nebeSquareDataRow13 : Array ℤ := #[-2, 2, 0, 1, 2, -2, 1, 1, 0, 0, 1, 1, 1, -1, 0, 0, 0, -1, 1, -1, 0, 1, 0, 1, 0, 0, -1, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0]
private def nebeSquareDataRow14 : Array ℤ := #[-1, -4, 1, 5, 3, 3, -5, -3, 0, -3, -5, 1, -4, -1, 1, -1, -2, -4, -1, 1, -1, -1, -1, 1, 1, -1, 1, -2, 1, 0, 1, 2, 1, 1, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1, 1, 0, 1]
private def nebeSquareDataRow15 : Array ℤ := #[-2, 0, -3, 6, 1, 6, -4, 0, -5, -2, -6, -2, -1, -1, 1, 0, 1, 1, 2, 1, -1, -2, 1, 0, 0, 0, 0, 3, 0, -5, -4, 0, 3, -3, 2, -1, 2, 1, 0, 2, -1, 0, 3, 1, 2, -1, 0, 1]
private def nebeSquareDataRow16 : Array ℤ := #[-8, -2, 0, 7, 2, 5, -8, -4, -4, 0, -6, 0, -4, -2, 1, -2, -1, -2, 2, 1, -2, -2, -1, 1, 1, -2, 0, -2, 2, 0, 0, 2, 0, -1, 0, 0, 2, 1, -2, -1, 1, 1, 1, 0, 1, -1, -1, 2]
private def nebeSquareDataRow17 : Array ℤ := #[6, -1, 0, -1, -2, -1, 8, 3, 7, -5, 2, 1, 8, 1, -3, -2, 1, 2, -1, 1, -1, 4, -2, -3, 0, 0, 2, 0, -2, 1, 1, 1, 0, 1, -2, 2, -1, -2, 0, 0, -1, 0, 0, -1, 1, 0, 0, 0]
private def nebeSquareDataRow18 : Array ℤ := #[7, 5, 0, -7, -3, -7, 10, 5, 5, 1, 6, 0, 6, 2, -1, 1, 3, 4, -1, 0, 1, 2, 1, -2, -2, 1, 0, 2, -2, 0, -1, -1, -2, 0, -2, 2, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 1, -1]
private def nebeSquareDataRow19 : Array ℤ := #[1, 6, -4, -2, 5, -5, 3, 2, 1, 2, 2, 0, 0, -2, 3, 1, -1, -2, 0, 1, -1, 2, -1, 1, -1, 1, -1, -1, 0, 2, 0, -2, 0, 2, 0, -1, -1, -1, 2, 0, 0, -1, -1, -2, 0, 2, 1, -2]
private def nebeSquareDataRow20 : Array ℤ := #[-13, 7, -6, 1, 6, -2, -9, -3, -11, 11, -1, -4, -10, -5, 5, 1, 0, -2, 2, 2, 0, -3, 0, 3, 0, -1, -4, -2, 5, 1, -2, -1, -2, -1, 0, -2, 2, 2, -2, 0, 2, -1, 0, 0, 0, 0, -1, -1]
private def nebeSquareDataRow21 : Array ℤ := #[-4, -5, 1, 6, 6, 3, -11, -5, -4, 0, -7, -1, -9, -3, 3, -1, -3, -6, 0, 1, -1, -3, -1, 2, 2, -2, 0, -3, 1, 1, 2, 2, 2, 1, 2, -1, 1, -1, 0, -1, 0, 0, -1, -1, 2, 1, 0, 0]
private def nebeSquareDataRow22 : Array ℤ := #[-6, -1, -2, 5, 6, 3, -10, -4, -6, 2, -7, -1, -9, -3, 4, 0, -3, -4, 1, 0, -1, -3, 0, 3, 1, -1, 0, -2, 2, 0, 0, 0, 2, 0, 2, -2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
private def nebeSquareDataRow23 : Array ℤ := #[-7, 2, -6, 0, 4, 1, -3, -1, -4, 4, 1, -1, -2, -3, 2, -1, 0, -1, 1, 2, 0, 1, 0, 2, -1, 2, -1, -2, 2, 1, -1, -2, -2, 0, -2, -1, -1, 2, -1, 0, 1, -1, -1, 1, -1, 0, -1, 1]
private def nebeSquareDataRow24 : Array ℤ := #[9, 3, -2, -5, 0, -4, 8, 6, 4, -2, 2, 1, 4, 2, 0, 2, 1, 3, -2, -2, 1, 1, 2, 0, -2, 2, 1, 2, -1, -3, -2, -3, 1, 1, 0, 0, 0, 0, 2, 2, -2, 0, 0, 0, -1, 1, 1, 0]
private def nebeSquareDataRow25 : Array ℤ := #[7, -5, 4, 1, -5, 2, 2, 1, 3, -5, -2, 0, 2, 3, -2, 0, 0, 2, -1, -2, 0, -2, 1, -2, 1, -1, 2, 2, -2, -3, 1, 2, 2, -1, 1, 1, 1, 0, 0, 1, -2, 1, 1, 0, 1, -1, 0, 0]
private def nebeSquareDataRow26 : Array ℤ := #[3, -1, 0, 0, -1, 1, -1, 0, 1, -1, -3, 1, -1, 1, 1, 1, 1, 0, 0, 0, -1, -1, 1, 1, -1, 0, 0, 1, 0, -2, -1, 0, 1, -1, 1, 0, 1, 1, 0, -1, 0, 0, 1, -1, 0, -1, 1, 1]
private def nebeSquareDataRow27 : Array ℤ := #[13, -4, 5, -6, -6, -2, 7, 3, 7, -5, 2, 3, 5, 3, -2, 1, 1, 2, -2, -4, 1, 1, 1, -1, 1, 1, 2, 3, -4, -1, 2, -1, 3, 2, 1, 1, -1, -1, 3, 1, -1, 0, -1, -1, 0, -1, 2, 0]
private def nebeSquareDataRow28 : Array ℤ := #[16, 0, 11, -8, -12, -8, 14, 5, 12, -5, 7, 2, 10, 8, -5, 1, 3, 6, -4, -4, 1, 1, 1, -5, 1, -2, 3, 4, -5, 0, 2, 2, 0, 0, 0, 4, -1, -2, 1, 0, -1, 1, -1, -2, 0, -1, 2, -2]
private def nebeSquareDataRow29 : Array ℤ := #[-12, -3, -4, 5, 6, 6, -14, -7, -8, 5, -6, -1, -12, -6, 4, 1, -4, -7, 3, 2, -2, -3, -2, 5, 2, 0, -2, -5, 4, 3, 2, 0, 2, 1, 1, -3, 1, 1, 0, -1, 2, -1, 0, -1, 2, -1, -1, 0]
private def nebeSquareDataRow30 : Array ℤ := #[1, -4, 6, 1, -4, -1, 0, -2, 3, -3, 0, 2, 2, 2, -2, -2, 0, 1, 0, -3, 0, 0, 0, -1, 2, -2, 1, 1, -2, 1, 2, 1, 1, 0, 1, 2, -1, -1, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0]
private def nebeSquareDataRow31 : Array ℤ := #[12, 3, 4, -10, -6, -8, 15, 5, 10, -2, 9, 1, 8, 5, -4, 2, 2, 5, -4, 0, 1, 3, 1, -5, -2, 0, 2, 1, -3, 1, 1, 0, -3, 0, -1, 3, -2, -1, 1, -1, -1, 0, -1, -1, -1, 1, 1, -1]
private def nebeSquareDataRow32 : Array ℤ := #[5, 0, -5, -1, -3, 2, 8, 3, 5, -4, 2, 0, 7, 1, -2, 0, 0, 4, 1, 1, -2, 3, 0, -2, -2, 2, 1, 1, -1, -2, -1, -1, 0, -1, -1, 1, -1, 1, 0, 1, -2, 0, 2, 0, 0, -1, -1, 0]
private def nebeSquareDataRow33 : Array ℤ := #[-10, 2, -3, 9, 6, 5, -8, -1, -8, 1, -6, -2, -3, -4, 2, -1, 0, -3, 4, 1, -1, -2, -1, 2, 1, 0, -1, 0, 1, -1, -2, 0, 2, -1, 1, -2, 2, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0]
private def nebeSquareDataRow34 : Array ℤ := #[3, -1, 6, -4, -2, -5, 2, 0, 5, 1, 5, 1, 1, 3, -2, 1, 1, -1, -2, 0, 2, 0, 0, -1, 0, 0, 0, -1, -1, 3, 2, 1, -2, 1, 0, 1, -2, -2, 0, -2, 0, 0, -2, -1, -1, 1, 1, -2]
private def nebeSquareDataRow35 : Array ℤ := #[7, -1, 5, -6, -5, -5, 7, 1, 7, -1, 7, 3, 4, 4, -2, 1, 0, 1, -2, -3, 2, 2, 1, 0, 0, 1, 0, 2, -2, 2, 2, -1, 0, 2, 0, 1, -3, -1, 2, 0, 0, 0, -2, 0, -2, 1, 1, -2]
private def nebeSquareDataRow36 : Array ℤ := #[-4, -6, -6, 3, 7, 5, -6, -3, -1, -1, -4, 1, -4, -5, 2, -2, -3, -5, 1, 2, -1, 2, -2, 3, 0, 2, 0, -4, 2, 2, 2, -1, 1, 3, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0, 0, 1, -1, 2]
private def nebeSquareDataRow37 : Array ℤ := #[3, 0, 9, -4, -4, -5, 3, 0, 4, 1, 5, 0, 1, 3, -3, 1, 1, 0, -2, 0, 1, 0, -1, -3, 2, -2, 1, -1, -2, 4, 3, 2, -1, 0, 0, 2, -1, -2, 0, -2, 1, 0, -2, -2, 1, 0, 1, -2]
private def nebeSquareDataRow38 : Array ℤ := #[0, 6, 5, -5, -1, -9, 2, -1, 2, 5, 4, 1, -3, 2, 1, 2, -1, 0, -2, -1, 0, -1, 0, 0, 0, -3, -1, -2, 1, 4, 2, 1, -3, 1, 0, 1, 0, -1, 0, -2, 2, 1, -2, -2, -1, 1, 1, -2]
private def nebeSquareDataRow39 : Array ℤ := #[5, -1, 9, -5, 0, -7, 2, 0, 3, 1, 3, 2, -1, 1, -1, 0, 2, -2, -3, -2, 3, 0, 0, -1, 2, -2, 0, 0, -2, 4, 3, 1, 0, 3, 1, 1, -1, -3, 1, -2, 1, 0, -3, -1, 0, 2, 2, -1]
private def nebeSquareDataRow40 : Array ℤ := #[4, -1, 6, -3, -3, -2, 2, 2, 3, -1, 2, 0, 3, 4, -3, 0, 4, 2, -2, 0, 3, 0, 1, -2, 0, 0, 1, 2, -2, 0, -1, 1, -1, -1, 0, 1, -1, -1, -1, -1, 0, 0, -1, 1, -1, 0, 1, 0]
private def nebeSquareDataRow41 : Array ℤ := #[-8, -3, -6, 7, 10, 7, -15, -5, -7, 2, -10, -1, -13, -5, 6, 1, -4, -8, 1, 4, -2, -4, -1, 5, 0, 1, -1, -5, 4, 0, 0, 0, 2, 1, 2, -4, 2, 1, 0, -1, 1, -1, 0, 0, 1, 0, -1, 1]
private def nebeSquareDataRow42 : Array ℤ := #[11, -8, 10, -6, -6, -4, 7, 0, 12, -5, 2, 5, 3, 4, -5, 0, 0, 0, -4, -2, 0, 1, -1, -2, 1, -2, 3, -3, -2, 4, 6, 2, 1, 3, 0, 3, -1, -3, 0, -3, 0, 1, -2, -3, 2, 0, 1, 0]
private def nebeSquareDataRow43 : Array ℤ := #[2, -3, 2, -1, -3, 0, 2, -1, 4, -2, 3, 1, 2, 2, -2, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, 1, 1, 0, 0, 0, 0, 1, -2, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]
private def nebeSquareDataRow44 : Array ℤ := #[4, -7, 12, -1, -5, -2, -2, -3, 3, -2, 0, 2, -2, 3, -3, -1, 0, -1, -3, -3, 2, -2, 0, -1, 4, -3, 2, 0, -2, 2, 4, 3, 1, 1, 1, 2, 0, -2, 0, -1, 1, 1, -2, 0, 1, 0, 1, 0]
private def nebeSquareDataRow45 : Array ℤ := #[1, -6, 1, 3, 2, 5, -5, -2, -1, -3, -7, 2, -4, -1, 1, -1, -2, -2, 0, -1, 0, -2, 0, 2, 1, 0, 2, -1, 0, -1, 1, 0, 3, 1, 1, -1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2]
private def nebeSquareDataRow46 : Array ℤ := #[-9, 2, -5, 3, 8, 1, -9, -4, -6, 5, -1, -3, -8, -4, 4, 1, -3, -6, 1, 4, 0, 0, -2, 2, 0, 0, -3, -3, 3, 3, 0, 0, -1, 0, 1, -3, -1, -1, 0, -1, 1, -2, -1, 0, 0, 2, -1, -2]
private def nebeSquareDataRow47 : Array ℤ := #[-4, 2, 3, -1, -3, -2, -3, -2, -4, 5, 0, -1, -4, 0, 0, 1, 1, 2, 1, -1, 1, -4, 1, 0, 1, -2, -1, 0, 1, 0, 0, 1, -1, -2, 1, 0, 1, 1, -2, 0, 1, 1, 1, 0, 1, -1, 0, -1]

private def nebeSquareData : Array (Array ℤ) := #[
  nebeSquareDataRow0, nebeSquareDataRow1, nebeSquareDataRow2, nebeSquareDataRow3,
  nebeSquareDataRow4, nebeSquareDataRow5, nebeSquareDataRow6, nebeSquareDataRow7,
  nebeSquareDataRow8, nebeSquareDataRow9, nebeSquareDataRow10, nebeSquareDataRow11,
  nebeSquareDataRow12, nebeSquareDataRow13, nebeSquareDataRow14, nebeSquareDataRow15,
  nebeSquareDataRow16, nebeSquareDataRow17, nebeSquareDataRow18, nebeSquareDataRow19,
  nebeSquareDataRow20, nebeSquareDataRow21, nebeSquareDataRow22, nebeSquareDataRow23,
  nebeSquareDataRow24, nebeSquareDataRow25, nebeSquareDataRow26, nebeSquareDataRow27,
  nebeSquareDataRow28, nebeSquareDataRow29, nebeSquareDataRow30, nebeSquareDataRow31,
  nebeSquareDataRow32, nebeSquareDataRow33, nebeSquareDataRow34, nebeSquareDataRow35,
  nebeSquareDataRow36, nebeSquareDataRow37, nebeSquareDataRow38, nebeSquareDataRow39,
  nebeSquareDataRow40, nebeSquareDataRow41, nebeSquareDataRow42, nebeSquareDataRow43,
  nebeSquareDataRow44, nebeSquareDataRow45, nebeSquareDataRow46, nebeSquareDataRow47
]

/-- Candidate square of the raw table, established by the product certificate below. -/
private def nebeSquare : Matrix (Fin 48) (Fin 48) ℤ :=
  fun i j => (nebeSquareData.getD i.val #[]).getD j.val 0

private def nebeColumnsDataRow0 : Array ℤ := #[-6, -1, -19, 6, -8, -4, -12, 5, 4, -9, 13, 11, -1, -4, -2, 20, 0, 2, -8, 4, 0, -1, 4, -4, 1, -13, -3, 0, -26, 12, 2, -5, 12, 3, 0, 2, 21, 4, -22, -1, -5, 4, -8, 13, -3, 7, 20, 0]
private def nebeColumnsDataRow1 : Array ℤ := #[2, 0, 3, 4, -3, 2, 2, 0, 2, 5, -2, -4, -3, -1, 4, -2, 3, 2, 0, -4, 1, 4, -2, 0, -3, 6, 0, -2, 2, 1, -1, 1, -3, -2, 0, -2, -1, -3, 6, 0, 0, 3, -1, -1, 3, 2, -4, 3]
private def nebeColumnsDataRow2 : Array ℤ := #[-7, -1, -6, -9, 0, 1, -10, 5, -2, -12, 13, 10, -1, 0, 6, 9, 4, 0, -4, 7, -7, 5, 3, 4, 2, -8, 6, 6, -12, 3, 5, 0, 4, 2, 1, 2, 14, 0, -15, 2, -7, 10, 3, 5, 0, 5, 5, -7]
private def nebeColumnsDataRow3 : Array ℤ := #[2, 1, 12, -6, 8, 0, 8, -4, -3, 4, -11, -5, 6, -1, -4, -10, -5, -3, 2, 0, 0, -4, -2, 3, 1, 6, -2, 1, 16, -9, -1, 4, -4, -3, 1, 2, -15, 2, 10, 1, 3, -7, 3, -7, -2, -8, -10, -2]
private def nebeColumnsDataRow4 : Array ℤ := #[6, 3, 7, 3, 0, 2, 5, -1, 0, 11, -12, -6, 2, 2, -3, -8, -2, -2, 3, -4, 2, -2, -2, -1, -1, 7, -4, -1, 12, -4, 0, 0, -7, 0, -1, 3, -14, -1, 14, -2, 2, -6, 0, -2, 5, -2, -10, 4]
private def nebeColumnsDataRow5 : Array ℤ := #[3, 1, 8, -3, 6, 0, 8, -5, -2, 4, -10, -5, 5, 0, -6, -9, -5, -3, 4, 0, 2, -6, 0, 1, 2, 3, -2, -1, 13, -7, -2, 1, -3, -2, 0, 1, -12, 1, 8, 1, 5, -9, 1, -7, -4, -6, -6, -1]
private def nebeColumnsDataRow6 : Array ℤ := #[-7, -5, -16, 10, -10, -5, -6, 6, 5, -9, 13, 6, -8, -8, 1, 16, 3, 4, -10, -1, 1, 2, -1, -6, -2, -8, -2, -3, -23, 11, -4, -4, 11, -1, 0, -5, 17, 2, -16, -2, -1, 11, -8, 8, -6, 4, 20, 0]
private def nebeColumnsDataRow7 : Array ℤ := #[-1, 0, -7, 6, -7, -1, -3, 3, 3, -2, 3, 0, -3, -3, 0, 4, 1, 1, -5, -1, 3, 0, 0, -3, -1, -2, -4, -3, -8, 7, -1, -4, 4, -1, 0, 0, 6, 1, -3, -2, -1, 5, -3, 4, -1, 3, 8, 2]
private def nebeColumnsDataRow8 : Array ℤ := #[-8, -5, -14, 4, -5, -7, -7, 6, 2, -11, 13, 9, -4, -7, -1, 16, 1, 2, -7, 2, -2, 1, 0, -4, -1, -10, 1, 0, -19, 6, -2, 0, 12, 0, 1, -3, 14, 4, -17, -2, -1, 8, -7, 9, -6, 1, 17, -3]
private def nebeColumnsDataRow9 : Array ℤ := #[4, 2, 5, 0, 0, 4, 2, -2, 0, 7, -3, -4, -1, 6, 5, -6, 3, 0, 6, -2, 1, 4, 0, 2, -1, 5, 3, -1, 6, -2, 2, 1, -6, 1, 0, 0, -3, -5, 8, 1, -1, -1, 3, -2, 6, 2, -9, 4]
private def nebeColumnsDataRow10 : Array ℤ := #[-4, -3, -7, 4, -7, -1, -5, 4, 2, -7, 10, 2, -7, -3, 6, 7, 6, 4, -4, 0, 0, 6, 0, -2, -2, -4, 3, -2, -11, 5, -1, -3, 4, 1, -1, -5, 11, -1, -6, -2, -1, 11, -1, 3, -1, 5, 8, -2]
private def nebeColumnsDataRow11 : Array ℤ := #[-3, -2, -4, -1, -1, -1, -3, 4, 0, -4, 4, 4, -1, -2, 0, 4, 0, 0, -3, 1, -2, 1, 1, -1, 1, -3, 0, 1, -5, 2, -1, 1, 2, 0, 1, 0, 4, 2, -5, 0, 0, 4, -1, 2, -1, 1, 5, -3]
private def nebeColumnsDataRow12 : Array ℤ := #[-6, -5, -10, 7, -7, -6, -3, 4, 2, -11, 9, 2, -6, -9, -1, 10, 2, 3, -10, 0, 2, 1, -2, -5, -2, -6, -2, -3, -13, 7, -5, -4, 9, -1, 0, -6, 9, 5, -10, -2, 2, 11, -4, 2, -8, 0, 16, -3]
private def nebeColumnsDataRow13 : Array ℤ := #[-5, -2, -5, -2, -3, -2, -5, 4, 0, -8, 8, 5, -2, -3, 3, 6, 1, 1, -3, 4, -2, 3, 2, 1, 0, -5, 2, 1, -9, 4, 0, 0, 5, 0, 1, -1, 10, 1, -9, 0, -4, 6, -1, 4, -2, 2, 7, -3]
private def nebeColumnsDataRow14 : Array ℤ := #[4, 3, 5, 0, 2, 2, 3, -3, 0, 7, -7, -3, 3, 3, -1, -5, -2, -1, 4, -2, 2, -1, 0, 1, 0, 5, -2, -1, 7, -3, 1, 2, -4, 0, 0, 3, -6, -1, 7, 0, 0, -7, 0, -1, 4, -1, -7, 3]
private def nebeColumnsDataRow15 : Array ℤ := #[0, 1, -1, 0, -2, 2, -1, 1, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 1, 3, 0, 1, 1, 0, 0, -1, 1, 1, 0, 0, -1, 0, 1, 3, -3, 0, -1, -1, 1, -2, 2, 2, 3, 0, 1]
private def nebeColumnsDataRow16 : Array ℤ := #[0, 1, -2, 2, -4, 1, -3, 2, 2, -1, 2, -1, -2, 0, 2, 1, 2, 0, -2, 0, 1, 2, 0, -1, -1, -1, -2, -1, -3, 4, 1, -3, 0, 1, 0, 0, 3, 1, -1, 1, -2, 4, 1, 2, 2, 3, 3, 2]
private def nebeColumnsDataRow17 : Array ℤ := #[-2, -2, -5, 2, -2, -2, -2, 1, 0, -5, 6, 3, -3, -1, 1, 3, 1, 2, -3, 1, 1, 0, -1, -1, -1, -3, 0, -1, -7, 6, -2, -1, 4, -1, 0, -2, 7, 1, -5, 1, -2, 3, 0, 1, -3, 0, 7, 0]
private def nebeColumnsDataRow18 : Array ℤ := #[2, 1, 4, -1, 2, 1, 3, -2, 0, 2, -4, -4, 1, 0, -1, -6, -1, -1, 1, -2, 2, -1, 0, 0, 0, 4, -1, -1, 7, -2, -1, 1, -2, -2, 0, 0, -5, 0, 6, 0, 3, -1, 2, -4, 0, -2, -4, 0]
private def nebeColumnsDataRow19 : Array ℤ := #[1, -1, 4, 3, 0, -2, 6, -2, 1, 6, -6, -4, 0, -1, -2, -1, -1, -1, 4, -2, 0, 0, -2, -1, -1, 3, 0, -2, 4, -6, -2, 2, -1, 0, 0, -3, -7, -1, 4, 0, 3, -4, -4, -1, -1, -2, -3, 3]
private def nebeColumnsDataRow20 : Array ℤ := #[-1, 0, -2, 0, -4, 1, -3, 3, 0, -2, 2, 1, -2, 1, 3, 1, 2, 0, -1, 2, 0, 3, 1, 0, 0, -2, 0, 0, -3, 3, 1, -3, -1, 2, 0, 1, 4, 0, -1, 0, -3, 4, 1, 2, 2, 3, 2, -1]
private def nebeColumnsDataRow21 : Array ℤ := #[-1, -2, -3, 5, -3, -2, 0, 1, 1, -2, 2, 0, -3, -4, -2, 4, 1, 2, -3, -1, 1, 0, -2, -2, -2, -3, -1, -2, -5, 1, -3, -2, 2, 1, -1, -3, 1, 2, -2, -1, 2, 2, -3, 0, -3, 0, 5, -1]
private def nebeColumnsDataRow22 : Array ℤ := #[0, 1, -1, -1, -2, 1, -3, 2, 0, -1, 1, 1, 0, 1, 2, -1, 0, 0, -1, 1, 0, 1, 2, 0, 0, 0, -1, 0, -1, 4, 1, -1, 0, 0, 0, 2, 3, 0, 0, 0, -3, 1, 2, 2, 2, 2, 1, 0]
private def nebeColumnsDataRow23 : Array ℤ := #[3, 2, 3, 0, 0, 2, 1, 0, 0, 4, -5, -3, 2, 2, 0, -5, -1, -1, 2, -1, 2, 0, 2, 0, 1, 3, -2, -1, 7, -1, 1, 0, -4, 0, 0, 2, -5, 0, 7, -1, 1, -2, 1, -1, 4, 0, -4, 1]
private def nebeColumnsDataRow24 : Array ℤ := #[1, 2, 1, -3, 3, 2, -2, -2, -1, -1, 1, 1, 2, 2, 0, 0, 1, 0, 0, 1, -1, -1, 0, 2, 1, -1, 1, 2, 1, -1, 3, -1, -1, 1, -1, 2, 0, 0, -1, 1, -1, -1, 3, -1, 1, 1, -3, -1]
private def nebeColumnsDataRow25 : Array ℤ := #[1, 0, -1, 4, -4, -1, 1, 1, 1, 1, -3, -3, -1, -1, -1, -1, 0, 0, 0, -1, 3, 0, 1, -3, 0, 1, -3, -3, 2, 1, -1, -2, 0, 0, -1, -1, -2, 1, 4, -2, 2, 1, -2, 0, 0, 1, 2, 1]
private def nebeColumnsDataRow26 : Array ℤ := #[-1, -1, -3, 0, 1, -2, -1, 0, -1, -3, 3, 3, 0, -1, -2, 3, 0, 0, -1, 1, -1, -2, -1, 0, 0, -3, 1, 1, -3, 1, 0, 0, 3, -1, 0, 0, 2, 1, -4, 0, 0, 0, -1, 1, -3, -1, 3, -1]
private def nebeColumnsDataRow27 : Array ℤ := #[-1, 1, -1, 0, -3, 1, -3, 1, 1, -3, 1, 0, 0, -1, 2, 1, 0, 1, -3, 2, 2, 2, 2, 0, 0, -1, -3, -1, -3, 4, 1, -3, 0, 1, 0, 1, 5, 2, -2, 1, -3, 2, 1, 1, 1, 2, 4, -1]
private def nebeColumnsDataRow28 : Array ℤ := #[2, 0, 4, 0, 2, 1, 4, -1, 0, 5, -4, -3, 1, 1, 0, -4, -1, -1, 3, -2, 0, -1, -1, 1, 0, 3, 1, 0, 6, -3, -1, 2, -3, -1, 1, 0, -6, -2, 5, 0, 2, -3, 0, -2, 1, -2, -5, 2]
private def nebeColumnsDataRow29 : Array ℤ := #[-1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 2, 1, -2, 0, 1, 3, 3, 0, 1, -1, -2, 2, -1, 0, 0, -1, 4, 1, -2, -3, 0, 1, 0, 1, -1, -2, 0, -2, -1, -1, 1, 3, -1, 0, 0, 1, -2, -1]
private def nebeColumnsDataRow30 : Array ℤ := #[-2, -1, -3, -2, 2, -1, -2, 0, -1, -3, 4, 4, 0, 1, 0, 4, 1, 0, 0, 1, -2, 0, 0, 0, 1, -3, 3, 2, -4, -1, 1, 1, 2, 1, 0, 0, 3, 0, -5, 0, 0, 1, 0, 1, -1, 0, 1, -2]
private def nebeColumnsDataRow31 : Array ℤ := #[-2, -1, 1, -3, 3, -1, 1, -1, -1, -1, 1, 2, 1, 0, 0, 2, 0, -1, 1, 2, -2, 0, -1, 2, 0, -2, 3, 2, -1, -3, 1, 2, 1, 0, 1, 0, 0, 0, -3, 2, -1, -1, 0, 0, -2, -2, -1, -1]
private def nebeColumnsDataRow32 : Array ℤ := #[2, 3, -1, 0, 1, 1, -1, -2, 1, 1, -2, -1, 3, 1, -3, -1, -2, -1, 0, 0, 2, -3, 2, 0, 2, 0, -3, 0, 1, 1, 2, -2, 0, 0, 0, 3, 0, 1, 0, -1, 0, -3, 0, 1, 1, 0, 0, 1]
private def nebeColumnsDataRow33 : Array ℤ := #[0, 0, -4, 3, -2, 0, -2, 2, 1, 0, 1, 1, -1, 0, -1, 3, 1, 0, -2, -1, 1, 0, 0, -2, 0, -2, -1, 0, -3, 2, 1, -2, 0, 1, 0, 1, 1, 1, -1, -1, 1, 2, -1, 2, 1, 1, 3, 0]
private def nebeColumnsDataRow34 : Array ℤ := #[0, 1, 1, -3, 1, 2, -1, 0, 0, 1, -1, 1, 2, 1, 1, -1, -1, -1, 0, 1, -1, 0, 2, 1, 2, 1, 0, 2, 1, 0, 1, 0, -2, 0, 0, 2, 1, -1, 0, 0, -2, 0, 1, 0, 2, 1, -2, -1]
private def nebeColumnsDataRow35 : Array ℤ := #[-2, -1, -3, 0, 0, -1, -2, 1, 0, -4, 5, 3, -2, -1, 0, 3, 1, 1, -2, 1, -1, 0, -1, 0, -1, -3, 1, 1, -5, 2, 0, 0, 3, 0, 0, -1, 4, 1, -5, 1, -1, 2, 0, 1, -2, 0, 4, -1]
private def nebeColumnsDataRow36 : Array ℤ := #[1, 1, 2, -1, 2, 1, 2, -1, 0, 3, -3, -1, 2, 1, -1, -2, -2, -1, 1, 0, 0, -2, 0, 1, 1, 2, -1, 1, 3, -1, 1, 1, -1, -1, 1, 2, -3, -1, 1, 1, 0, -3, 0, -1, 0, -1, -2, 2]
private def nebeColumnsDataRow37 : Array ℤ := #[2, 1, 3, -1, 2, 1, 2, -2, -1, 2, -2, -1, 1, 2, 0, -4, -1, 0, 3, 0, 1, -1, 0, 1, 0, 2, 0, -1, 4, -1, 0, 1, -1, -1, 0, 1, -2, -1, 3, 1, 0, -4, 1, -2, 0, -1, -3, 1]
private def nebeColumnsDataRow38 : Array ℤ := #[0, 1, -2, 1, -2, 1, -2, 1, 1, -1, 0, 0, 0, -1, 0, 1, 0, 1, -2, 0, 1, 0, 2, -1, 1, 0, -2, 0, -1, 2, 1, -2, 0, 0, -1, 1, 2, 0, 0, -2, 0, 2, -1, 1, 1, 2, 2, -1]
private def nebeColumnsDataRow39 : Array ℤ := #[2, 1, 0, 2, 0, 0, 0, -2, 0, 0, -1, -2, 1, 0, -1, -1, 0, 1, -1, -1, 2, -2, 0, -1, 0, 1, -2, -1, 2, 2, 0, -2, 0, 0, -1, 0, -1, 1, 2, -1, 1, -1, 1, -1, 0, 0, 0, 1]
private def nebeColumnsDataRow40 : Array ℤ := #[0, 0, 2, -1, 0, 1, 1, 0, 0, 1, -1, -1, -1, 1, 1, -1, 1, 0, 2, 0, -1, 2, 0, 1, 0, 1, 1, 0, 1, -2, 0, 1, -2, 1, 0, -1, -1, -1, 1, 1, 0, 0, 0, -1, 1, 1, -2, 0]
private def nebeColumnsDataRow41 : Array ℤ := #[-1, -1, -1, -1, 1, -1, -1, 1, -1, -2, 2, 2, 0, 0, 0, 1, 0, 0, -1, 1, -1, 0, 0, 0, 0, -1, 1, 1, -1, 1, 0, 1, 1, 0, 1, 0, 1, 1, -2, 1, 0, 1, 1, 0, -1, -1, 1, -1]
private def nebeColumnsDataRow42 : Array ℤ := #[0, 0, 2, 0, 1, 0, 3, -1, 1, 2, -3, -2, 1, -1, -1, -2, -2, -1, 0, -1, 1, -1, 0, 0, 0, 2, -2, -1, 2, -1, -1, 1, 0, -2, 1, 0, -2, 0, 1, 1, 1, -2, -1, -1, -1, -2, 0, 1]
private def nebeColumnsDataRow43 : Array ℤ := #[0, -1, 2, 0, -1, 0, 1, 1, -1, 0, -2, -1, 0, 0, 1, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, -1, 2, 0, -1, -1, -2, 1, 0, 0, -2, 1, 2, 1, 0, 0, 1, -1, 0, 0, 0, -1]
private def nebeColumnsDataRow44 : Array ℤ := #[1, 1, 0, 0, 2, 0, 1, -2, 1, 2, -1, -1, 1, 1, -2, -1, -1, -1, 1, -1, 0, -2, 0, 0, 1, 1, 0, 1, 1, -1, 1, 0, 0, -1, 0, 0, -1, -1, 0, 0, 1, -2, 0, 0, 0, -1, -1, 2]
private def nebeColumnsDataRow45 : Array ℤ := #[-1, -1, 0, 0, -1, 0, 0, 2, 0, 0, 0, 1, -1, -1, 1, 1, 0, 0, -1, 0, -1, 1, -1, 0, 0, 0, 0, 1, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, -1, -1, 2, -1, 1, 1, 0, 0, -1]
private def nebeColumnsDataRow46 : Array ℤ := #[0, 1, -2, 0, -1, 1, -3, 1, 1, -1, 2, 1, 0, 0, 1, 2, 1, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 1, -2, 2, 2, -1, 0, 0, 0, 1, 3, 0, -2, 0, -1, 2, 0, 2, 2, 2, 1, 0]
private def nebeColumnsDataRow47 : Array ℤ := #[1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -2, -2, -1, 0, 0, 0, 0, -2, -1, 0, 0, 0, -1, 0, 2, 0, -1, 0, -1, 0, 0, 0, -3, 1, 1, 1, 1, -2, 1, -2, -1, -1, 0, 0]

private def nebeColumnsData : Array (Array ℤ) := #[
  nebeColumnsDataRow0, nebeColumnsDataRow1, nebeColumnsDataRow2, nebeColumnsDataRow3,
  nebeColumnsDataRow4, nebeColumnsDataRow5, nebeColumnsDataRow6, nebeColumnsDataRow7,
  nebeColumnsDataRow8, nebeColumnsDataRow9, nebeColumnsDataRow10, nebeColumnsDataRow11,
  nebeColumnsDataRow12, nebeColumnsDataRow13, nebeColumnsDataRow14, nebeColumnsDataRow15,
  nebeColumnsDataRow16, nebeColumnsDataRow17, nebeColumnsDataRow18, nebeColumnsDataRow19,
  nebeColumnsDataRow20, nebeColumnsDataRow21, nebeColumnsDataRow22, nebeColumnsDataRow23,
  nebeColumnsDataRow24, nebeColumnsDataRow25, nebeColumnsDataRow26, nebeColumnsDataRow27,
  nebeColumnsDataRow28, nebeColumnsDataRow29, nebeColumnsDataRow30, nebeColumnsDataRow31,
  nebeColumnsDataRow32, nebeColumnsDataRow33, nebeColumnsDataRow34, nebeColumnsDataRow35,
  nebeColumnsDataRow36, nebeColumnsDataRow37, nebeColumnsDataRow38, nebeColumnsDataRow39,
  nebeColumnsDataRow40, nebeColumnsDataRow41, nebeColumnsDataRow42, nebeColumnsDataRow43,
  nebeColumnsDataRow44, nebeColumnsDataRow45, nebeColumnsDataRow46, nebeColumnsDataRow47
]

section IntegerCertificates

private theorem sumOfFn_eq {n : ℕ} (f : Fin n → ℤ) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ, ih]

private theorem dotOfFn_eq {n : ℕ} (f g : Fin n → ℤ) :
    (List.zipWith (· * ·) (List.ofFn f) (List.ofFn g)).sum = ∑ i, f i * g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.sum_cons,
      Fin.sum_univ_succ, ih]

private theorem arrayRow_eq (a : Array ℤ) (ha : a.size = 48) :
    List.ofFn (fun k : Fin 48 => a.getD k.val 0) = a.toList := by
  apply List.ext_getElem
  · simpa using ha.symm
  · intro i hi hj
    rw [List.getElem_ofFn, Array.getElem_toList, Array.getElem_eq_getD 0]

private theorem nebeOrderThreeData_shape (i : Fin 48) :
    (nebeOrderThreeData.getD i.val #[]).size = 48 := by
  fin_cases i <;> rfl

private theorem nebeSquareData_shape (i : Fin 48) :
    (nebeSquareData.getD i.val #[]).size = 48 := by
  fin_cases i <;> rfl

private theorem nebeColumns_eq (j : Fin 48) :
    (nebeColumnsData.getD j.val #[]).toList =
      List.ofFn (fun k : Fin 48 => nebeOrderThree k j) := by
  fin_cases j <;> decide +kernel

private def mulRow (a : Array ℤ) : List ℤ :=
  List.ofFn fun j : Fin 48 =>
    (List.zipWith (· * ·) a.toList (nebeColumnsData.getD j.val #[]).toList).sum

private theorem mul_eq_of_row_checks (data : Array (Array ℤ))
    (A B : Matrix (Fin 48) (Fin 48) ℤ)
    (ha : ∀ i k : Fin 48, A i k = (data.getD i.val #[]).getD k.val 0)
    (hs : ∀ i : Fin 48, (data.getD i.val #[]).size = 48)
    (h : ∀ i : Fin 48, mulRow (data.getD i.val #[]) = List.ofFn (B i)) :
    A * nebeOrderThree = B := by
  apply Matrix.ext
  intro i j
  have hj := congrArg (fun xs : List ℤ => xs[j.val]?) (h i)
  simp only [mulRow, List.getElem?_ofFn, j.isLt, dite_true, Option.some.injEq] at hj
  rw [Matrix.mul_apply, ← dotOfFn_eq]
  have hrow : A i = fun k => (data.getD i.val #[]).getD k.val 0 := funext (ha i)
  rw [hrow, arrayRow_eq _ (hs i), ← nebeColumns_eq j]
  exact hj

private theorem squareRow_0 :
    mulRow (nebeOrderThreeData.getD 0 #[]) = List.ofFn (nebeSquare (0 : Fin 48)) := by
  decide +kernel

private theorem squareRow_1 :
    mulRow (nebeOrderThreeData.getD 1 #[]) = List.ofFn (nebeSquare (1 : Fin 48)) := by
  decide +kernel

private theorem squareRow_2 :
    mulRow (nebeOrderThreeData.getD 2 #[]) = List.ofFn (nebeSquare (2 : Fin 48)) := by
  decide +kernel

private theorem squareRow_3 :
    mulRow (nebeOrderThreeData.getD 3 #[]) = List.ofFn (nebeSquare (3 : Fin 48)) := by
  decide +kernel

private theorem squareRow_4 :
    mulRow (nebeOrderThreeData.getD 4 #[]) = List.ofFn (nebeSquare (4 : Fin 48)) := by
  decide +kernel

private theorem squareRow_5 :
    mulRow (nebeOrderThreeData.getD 5 #[]) = List.ofFn (nebeSquare (5 : Fin 48)) := by
  decide +kernel

private theorem squareRow_6 :
    mulRow (nebeOrderThreeData.getD 6 #[]) = List.ofFn (nebeSquare (6 : Fin 48)) := by
  decide +kernel

private theorem squareRow_7 :
    mulRow (nebeOrderThreeData.getD 7 #[]) = List.ofFn (nebeSquare (7 : Fin 48)) := by
  decide +kernel

private theorem squareRow_8 :
    mulRow (nebeOrderThreeData.getD 8 #[]) = List.ofFn (nebeSquare (8 : Fin 48)) := by
  decide +kernel

private theorem squareRow_9 :
    mulRow (nebeOrderThreeData.getD 9 #[]) = List.ofFn (nebeSquare (9 : Fin 48)) := by
  decide +kernel

private theorem squareRow_10 :
    mulRow (nebeOrderThreeData.getD 10 #[]) = List.ofFn (nebeSquare (10 : Fin 48)) := by
  decide +kernel

private theorem squareRow_11 :
    mulRow (nebeOrderThreeData.getD 11 #[]) = List.ofFn (nebeSquare (11 : Fin 48)) := by
  decide +kernel

private theorem squareRow_12 :
    mulRow (nebeOrderThreeData.getD 12 #[]) = List.ofFn (nebeSquare (12 : Fin 48)) := by
  decide +kernel

private theorem squareRow_13 :
    mulRow (nebeOrderThreeData.getD 13 #[]) = List.ofFn (nebeSquare (13 : Fin 48)) := by
  decide +kernel

private theorem squareRow_14 :
    mulRow (nebeOrderThreeData.getD 14 #[]) = List.ofFn (nebeSquare (14 : Fin 48)) := by
  decide +kernel

private theorem squareRow_15 :
    mulRow (nebeOrderThreeData.getD 15 #[]) = List.ofFn (nebeSquare (15 : Fin 48)) := by
  decide +kernel

private theorem squareRow_16 :
    mulRow (nebeOrderThreeData.getD 16 #[]) = List.ofFn (nebeSquare (16 : Fin 48)) := by
  decide +kernel

private theorem squareRow_17 :
    mulRow (nebeOrderThreeData.getD 17 #[]) = List.ofFn (nebeSquare (17 : Fin 48)) := by
  decide +kernel

private theorem squareRow_18 :
    mulRow (nebeOrderThreeData.getD 18 #[]) = List.ofFn (nebeSquare (18 : Fin 48)) := by
  decide +kernel

private theorem squareRow_19 :
    mulRow (nebeOrderThreeData.getD 19 #[]) = List.ofFn (nebeSquare (19 : Fin 48)) := by
  decide +kernel

private theorem squareRow_20 :
    mulRow (nebeOrderThreeData.getD 20 #[]) = List.ofFn (nebeSquare (20 : Fin 48)) := by
  decide +kernel

private theorem squareRow_21 :
    mulRow (nebeOrderThreeData.getD 21 #[]) = List.ofFn (nebeSquare (21 : Fin 48)) := by
  decide +kernel

private theorem squareRow_22 :
    mulRow (nebeOrderThreeData.getD 22 #[]) = List.ofFn (nebeSquare (22 : Fin 48)) := by
  decide +kernel

private theorem squareRow_23 :
    mulRow (nebeOrderThreeData.getD 23 #[]) = List.ofFn (nebeSquare (23 : Fin 48)) := by
  decide +kernel

private theorem squareRow_24 :
    mulRow (nebeOrderThreeData.getD 24 #[]) = List.ofFn (nebeSquare (24 : Fin 48)) := by
  decide +kernel

private theorem squareRow_25 :
    mulRow (nebeOrderThreeData.getD 25 #[]) = List.ofFn (nebeSquare (25 : Fin 48)) := by
  decide +kernel

private theorem squareRow_26 :
    mulRow (nebeOrderThreeData.getD 26 #[]) = List.ofFn (nebeSquare (26 : Fin 48)) := by
  decide +kernel

private theorem squareRow_27 :
    mulRow (nebeOrderThreeData.getD 27 #[]) = List.ofFn (nebeSquare (27 : Fin 48)) := by
  decide +kernel

private theorem squareRow_28 :
    mulRow (nebeOrderThreeData.getD 28 #[]) = List.ofFn (nebeSquare (28 : Fin 48)) := by
  decide +kernel

private theorem squareRow_29 :
    mulRow (nebeOrderThreeData.getD 29 #[]) = List.ofFn (nebeSquare (29 : Fin 48)) := by
  decide +kernel

private theorem squareRow_30 :
    mulRow (nebeOrderThreeData.getD 30 #[]) = List.ofFn (nebeSquare (30 : Fin 48)) := by
  decide +kernel

private theorem squareRow_31 :
    mulRow (nebeOrderThreeData.getD 31 #[]) = List.ofFn (nebeSquare (31 : Fin 48)) := by
  decide +kernel

private theorem squareRow_32 :
    mulRow (nebeOrderThreeData.getD 32 #[]) = List.ofFn (nebeSquare (32 : Fin 48)) := by
  decide +kernel

private theorem squareRow_33 :
    mulRow (nebeOrderThreeData.getD 33 #[]) = List.ofFn (nebeSquare (33 : Fin 48)) := by
  decide +kernel

private theorem squareRow_34 :
    mulRow (nebeOrderThreeData.getD 34 #[]) = List.ofFn (nebeSquare (34 : Fin 48)) := by
  decide +kernel

private theorem squareRow_35 :
    mulRow (nebeOrderThreeData.getD 35 #[]) = List.ofFn (nebeSquare (35 : Fin 48)) := by
  decide +kernel

private theorem squareRow_36 :
    mulRow (nebeOrderThreeData.getD 36 #[]) = List.ofFn (nebeSquare (36 : Fin 48)) := by
  decide +kernel

private theorem squareRow_37 :
    mulRow (nebeOrderThreeData.getD 37 #[]) = List.ofFn (nebeSquare (37 : Fin 48)) := by
  decide +kernel

private theorem squareRow_38 :
    mulRow (nebeOrderThreeData.getD 38 #[]) = List.ofFn (nebeSquare (38 : Fin 48)) := by
  decide +kernel

private theorem squareRow_39 :
    mulRow (nebeOrderThreeData.getD 39 #[]) = List.ofFn (nebeSquare (39 : Fin 48)) := by
  decide +kernel

private theorem squareRow_40 :
    mulRow (nebeOrderThreeData.getD 40 #[]) = List.ofFn (nebeSquare (40 : Fin 48)) := by
  decide +kernel

private theorem squareRow_41 :
    mulRow (nebeOrderThreeData.getD 41 #[]) = List.ofFn (nebeSquare (41 : Fin 48)) := by
  decide +kernel

private theorem squareRow_42 :
    mulRow (nebeOrderThreeData.getD 42 #[]) = List.ofFn (nebeSquare (42 : Fin 48)) := by
  decide +kernel

private theorem squareRow_43 :
    mulRow (nebeOrderThreeData.getD 43 #[]) = List.ofFn (nebeSquare (43 : Fin 48)) := by
  decide +kernel

private theorem squareRow_44 :
    mulRow (nebeOrderThreeData.getD 44 #[]) = List.ofFn (nebeSquare (44 : Fin 48)) := by
  decide +kernel

private theorem squareRow_45 :
    mulRow (nebeOrderThreeData.getD 45 #[]) = List.ofFn (nebeSquare (45 : Fin 48)) := by
  decide +kernel

private theorem squareRow_46 :
    mulRow (nebeOrderThreeData.getD 46 #[]) = List.ofFn (nebeSquare (46 : Fin 48)) := by
  decide +kernel

private theorem squareRow_47 :
    mulRow (nebeOrderThreeData.getD 47 #[]) = List.ofFn (nebeSquare (47 : Fin 48)) := by
  decide +kernel

private theorem nebeSquare_eq : nebeOrderThree * nebeOrderThree = nebeSquare := by
  apply mul_eq_of_row_checks nebeOrderThreeData nebeOrderThree nebeSquare (fun _ _ => rfl) nebeOrderThreeData_shape
  intro i
  fin_cases i
  · exact squareRow_0
  · exact squareRow_1
  · exact squareRow_2
  · exact squareRow_3
  · exact squareRow_4
  · exact squareRow_5
  · exact squareRow_6
  · exact squareRow_7
  · exact squareRow_8
  · exact squareRow_9
  · exact squareRow_10
  · exact squareRow_11
  · exact squareRow_12
  · exact squareRow_13
  · exact squareRow_14
  · exact squareRow_15
  · exact squareRow_16
  · exact squareRow_17
  · exact squareRow_18
  · exact squareRow_19
  · exact squareRow_20
  · exact squareRow_21
  · exact squareRow_22
  · exact squareRow_23
  · exact squareRow_24
  · exact squareRow_25
  · exact squareRow_26
  · exact squareRow_27
  · exact squareRow_28
  · exact squareRow_29
  · exact squareRow_30
  · exact squareRow_31
  · exact squareRow_32
  · exact squareRow_33
  · exact squareRow_34
  · exact squareRow_35
  · exact squareRow_36
  · exact squareRow_37
  · exact squareRow_38
  · exact squareRow_39
  · exact squareRow_40
  · exact squareRow_41
  · exact squareRow_42
  · exact squareRow_43
  · exact squareRow_44
  · exact squareRow_45
  · exact squareRow_46
  · exact squareRow_47

private theorem cubeRow_0 :
    mulRow (nebeSquareData.getD 0 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (0 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_1 :
    mulRow (nebeSquareData.getD 1 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (1 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_2 :
    mulRow (nebeSquareData.getD 2 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (2 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_3 :
    mulRow (nebeSquareData.getD 3 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (3 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_4 :
    mulRow (nebeSquareData.getD 4 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (4 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_5 :
    mulRow (nebeSquareData.getD 5 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (5 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_6 :
    mulRow (nebeSquareData.getD 6 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (6 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_7 :
    mulRow (nebeSquareData.getD 7 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (7 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_8 :
    mulRow (nebeSquareData.getD 8 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (8 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_9 :
    mulRow (nebeSquareData.getD 9 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (9 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_10 :
    mulRow (nebeSquareData.getD 10 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (10 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_11 :
    mulRow (nebeSquareData.getD 11 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (11 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_12 :
    mulRow (nebeSquareData.getD 12 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (12 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_13 :
    mulRow (nebeSquareData.getD 13 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (13 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_14 :
    mulRow (nebeSquareData.getD 14 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (14 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_15 :
    mulRow (nebeSquareData.getD 15 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (15 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_16 :
    mulRow (nebeSquareData.getD 16 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (16 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_17 :
    mulRow (nebeSquareData.getD 17 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (17 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_18 :
    mulRow (nebeSquareData.getD 18 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (18 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_19 :
    mulRow (nebeSquareData.getD 19 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (19 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_20 :
    mulRow (nebeSquareData.getD 20 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (20 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_21 :
    mulRow (nebeSquareData.getD 21 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (21 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_22 :
    mulRow (nebeSquareData.getD 22 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (22 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_23 :
    mulRow (nebeSquareData.getD 23 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (23 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_24 :
    mulRow (nebeSquareData.getD 24 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (24 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_25 :
    mulRow (nebeSquareData.getD 25 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (25 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_26 :
    mulRow (nebeSquareData.getD 26 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (26 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_27 :
    mulRow (nebeSquareData.getD 27 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (27 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_28 :
    mulRow (nebeSquareData.getD 28 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (28 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_29 :
    mulRow (nebeSquareData.getD 29 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (29 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_30 :
    mulRow (nebeSquareData.getD 30 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (30 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_31 :
    mulRow (nebeSquareData.getD 31 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (31 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_32 :
    mulRow (nebeSquareData.getD 32 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (32 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_33 :
    mulRow (nebeSquareData.getD 33 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (33 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_34 :
    mulRow (nebeSquareData.getD 34 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (34 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_35 :
    mulRow (nebeSquareData.getD 35 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (35 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_36 :
    mulRow (nebeSquareData.getD 36 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (36 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_37 :
    mulRow (nebeSquareData.getD 37 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (37 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_38 :
    mulRow (nebeSquareData.getD 38 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (38 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_39 :
    mulRow (nebeSquareData.getD 39 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (39 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_40 :
    mulRow (nebeSquareData.getD 40 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (40 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_41 :
    mulRow (nebeSquareData.getD 41 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (41 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_42 :
    mulRow (nebeSquareData.getD 42 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (42 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_43 :
    mulRow (nebeSquareData.getD 43 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (43 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_44 :
    mulRow (nebeSquareData.getD 44 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (44 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_45 :
    mulRow (nebeSquareData.getD 45 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (45 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_46 :
    mulRow (nebeSquareData.getD 46 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (46 : Fin 48)) := by
  decide +kernel

private theorem cubeRow_47 :
    mulRow (nebeSquareData.getD 47 #[]) = List.ofFn ((1 : Matrix (Fin 48) (Fin 48) ℤ) (47 : Fin 48)) := by
  decide +kernel

private theorem nebeSquare_mul : nebeSquare * nebeOrderThree = (1 : Matrix (Fin 48) (Fin 48) ℤ) := by
  apply mul_eq_of_row_checks nebeSquareData nebeSquare (1 : Matrix (Fin 48) (Fin 48) ℤ) (fun _ _ => rfl) nebeSquareData_shape
  intro i
  fin_cases i
  · exact cubeRow_0
  · exact cubeRow_1
  · exact cubeRow_2
  · exact cubeRow_3
  · exact cubeRow_4
  · exact cubeRow_5
  · exact cubeRow_6
  · exact cubeRow_7
  · exact cubeRow_8
  · exact cubeRow_9
  · exact cubeRow_10
  · exact cubeRow_11
  · exact cubeRow_12
  · exact cubeRow_13
  · exact cubeRow_14
  · exact cubeRow_15
  · exact cubeRow_16
  · exact cubeRow_17
  · exact cubeRow_18
  · exact cubeRow_19
  · exact cubeRow_20
  · exact cubeRow_21
  · exact cubeRow_22
  · exact cubeRow_23
  · exact cubeRow_24
  · exact cubeRow_25
  · exact cubeRow_26
  · exact cubeRow_27
  · exact cubeRow_28
  · exact cubeRow_29
  · exact cubeRow_30
  · exact cubeRow_31
  · exact cubeRow_32
  · exact cubeRow_33
  · exact cubeRow_34
  · exact cubeRow_35
  · exact cubeRow_36
  · exact cubeRow_37
  · exact cubeRow_38
  · exact cubeRow_39
  · exact cubeRow_40
  · exact cubeRow_41
  · exact cubeRow_42
  · exact cubeRow_43
  · exact cubeRow_44
  · exact cubeRow_45
  · exact cubeRow_46
  · exact cubeRow_47

/-- The third power of Nebe's concrete matrix is the identity. -/
theorem nebeOrderThree_cube : nebeOrderThree ^ 3 = 1 := by
  rw [pow_succ, pow_two, nebeSquare_eq, nebeSquare_mul]

theorem nebeOrderThree_trace : nebeOrderThree.trace = 0 := by
  rw [Matrix.trace, ← sumOfFn_eq]
  decide +kernel

theorem nebeOrderThree_trace_square : (nebeOrderThree ^ 2).trace = 0 := by
  rw [pow_two, nebeSquare_eq, Matrix.trace, ← sumOfFn_eq]
  decide +kernel

end IntegerCertificates

/-- The concrete real column-coordinate action has fixed rank sixteen.
Identifying the abstract order-three group action with this concrete matrix
in Nebe's basis is external to the certificate. -/
theorem nebeOrderThree_fixedRank16 :
    Module.finrank ℝ (LinearMap.ker (rowAction ℝ nebeOrderThree - 1)) = 16 :=
  rowAction_fixedRank16_of_certificate ℝ nebeOrderThree
    nebeOrderThree_cube nebeOrderThree_trace nebeOrderThree_trace_square

#print axioms nebeOrderThree_fixedRank16
#print axioms nebeOrderThree_cube

end P48qFixedRankCertificateDraft
