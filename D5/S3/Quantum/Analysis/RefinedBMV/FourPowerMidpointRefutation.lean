/- GID: D5/S3/Quantum/Analysis/RefinedBMV/FourPowerMidpointRefutation
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Analysis/RefinedBMV/FourPowerMidpointRefutation.claim; result=D5/S3/Quantum/Analysis/RefinedBMV/FourPowerMidpointRefutation.result; claim=D5/S3/Quantum/Analysis/RefinedBMV/FourPowerMidpointRefutation.claim
   digest: A conditional four-copy midpoint trace refutation in dimension three. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A positive diagonal first factor and a symmetric involution give
a negative average over the 81 splits with both opposite totals equal to eight.
The sign is verified using integral matrices before normalizing the involution. -/

namespace RefinedBMV.FourPowerMidpointRefutation

open Matrix

private abbrev ZMat := Matrix (Fin 3) (Fin 3) ℤ
private abbrev RMat := Matrix (Fin 3) (Fin 3) ℝ

private def x : ZMat := diagonal ![100, 1, 10000]
private def y : ZMat :=
  !![-332929, 332928, 470832;
      332928, -332929, 470832;
      470832, 470832, 1]

private def splitSum {R : Type*} [Semiring R]
    (A B : Matrix (Fin 3) (Fin 3) R) : R :=
  ∑ i ∈ Finset.range 9, ∑ j ∈ Finset.range 9,
    trace (A ^ i * B * A ^ j * B * A ^ (8 - i) * B * A ^ (8 - j) * B)

private theorem symmetric_witness : yᵀ = y := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem square_witness : y ^ 2 = diagonal (fun _ ↦ (665857 : ℤ) ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem integer_trace_gap :
    splitSum x y < 81 * trace ((x ^ 4 * y) ^ 4) := by
  simp only [splitSum, x, Matrix.diagonal_pow]
  decide +kernel

private def toReal : ZMat →+* RMat := (Int.castRingHom ℝ).mapMatrix

private theorem toReal_transpose (M : ZMat) : toReal Mᵀ = (toReal M)ᴴ := by
  ext i j
  simp [toReal, Matrix.conjTranspose_apply]

private theorem toReal_diagonal (d : Fin 3 → ℤ) :
    toReal (diagonal d) = diagonal (fun i ↦ (d i : ℝ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [toReal]
  · simp [toReal, diagonal_apply_ne _ h]

private theorem toReal_trace (M : ZMat) : trace (toReal M) = ((trace M : ℤ) : ℝ) :=
  (AddMonoidHom.map_trace (Int.castRingHom ℝ) M).symm

private theorem toReal_splitSum (A B : ZMat) :
    splitSum (toReal A) (toReal B) = ((splitSum A B : ℤ) : ℝ) := by
  unfold splitSum
  simp only [Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← toReal_trace]
  simp only [map_mul, map_pow]

private theorem x_posDef : (toReal x).PosDef := by
  rw [x, toReal_diagonal, posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

/-- The four-copy midpoint comparison at fixed equal opposite totals for
positive definite first factors and self-adjoint involutions. -/
def claim : Prop :=
  ∀ A B : RMat, A.PosDef → B.IsHermitian → B ^ 2 = 1 →
    81 * trace ((A ^ 4 * B) ^ 4) ≤ splitSum A B

/-- Even averaging both splits with fixed opposite totals can miss the midpoint. -/
theorem result : ¬ claim := by
  intro h
  have hsym : (toReal y).IsHermitian := by
    change (toReal y)ᴴ = toReal y
    rw [← toReal_transpose, symmetric_witness]
  have hsq : (toReal y) ^ 2 = ((665857 : ℝ) ^ 2) • 1 := by
    rw [← map_pow, square_witness, toReal_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      norm_num [Matrix.one_apply]
    · simp [Matrix.one_apply, h]
  have hright : trace ((toReal x ^ 4 * toReal y) ^ 4) =
      ((trace ((x ^ 4 * y) ^ 4) : ℤ) : ℝ) := by
    rw [← toReal_trace]
    simp only [map_mul, map_pow]
  have hlt : splitSum (toReal x) (toReal y) <
      81 * trace ((toReal x ^ 4 * toReal y) ^ 4) := by
    rw [toReal_splitSum, hright]
    exact_mod_cast integer_trace_gap
  let c : ℝ := (665857 : ℝ)⁻¹
  let B : RMat := c • toReal y
  have hBstar : B.IsHermitian := by
    change (c • toReal y)ᴴ = c • toReal y
    rw [conjTranspose_smul, star_trivial, hsym.eq]
  have hBsq : B ^ 2 = 1 := by
    dsimp only [B]
    rw [smul_pow, hsq, smul_smul, ← mul_pow]
    norm_num [c]
  have hscale : splitSum (toReal x) B = c ^ 4 * splitSum (toReal x) (toReal y) := by
    unfold splitSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [B, Matrix.mul_smul, Matrix.smul_mul, smul_smul, trace_smul, smul_eq_mul]
    ring
  have hscaleRoot : trace ((toReal x ^ 4 * B) ^ 4) =
      c ^ 4 * trace ((toReal x ^ 4 * toReal y) ^ 4) := by
    simp only [B, Matrix.mul_smul, smul_pow, trace_smul, smul_eq_mul]
  have hlt' := mul_lt_mul_of_pos_left hlt (show 0 < c ^ 4 by norm_num [c])
  have hge := h (toReal x) B x_posDef hBstar hBsq
  rw [hscaleRoot, hscale] at hge
  exact (not_le_of_gt hlt') (by simpa only [mul_left_comm (81 : ℝ)] using hge)

end RefinedBMV.FourPowerMidpointRefutation
