/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit real Cartesian neutral chain and unbounded linear drift for every even polygon. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
import Mathlib.Analysis.Normed.Group.Bounded

/-! The source's radial/tangential chain, rotated to actual real Cartesian displacements. -/
noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
open InverseChordCirculant AlternatingPolygonSpectrum AlternatingPolygonModes
open AlternatingPolygonRealSpaces

def radial0 (m : ℕ) : RealCartesian m := Sum.elim (fun _ => 0) (fun _ => 1)
def radial1 (m : ℕ) : RealCartesian m :=
  Sum.elim (fun j => charge (2 * m) j / (1 - (m : ℝ) ^ 2 / 2)) (fun _ => 0)

def cartesian0 (m : ℕ) : RealCartesian m :=
  (AlternatingPolygonSpectrum.rotation (2 * m)).mulVec (radial0 m)
def cartesian1 (m : ℕ) : RealCartesian m :=
  (AlternatingPolygonSpectrum.rotation (2 * m)).mulVec (radial1 m)

private theorem charge_square (m : ℕ) (j : Fin (2 * m)) :
    charge (2 * m) j * charge (2 * m) j = 1 := by
  unfold charge
  rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private theorem block_radial_chain (m : ℕ) (hm : 1 ≤ m) :
    (Matrix.fromBlocks 0 (blockB m) (blockC m) 0).mulVec (radial0 m) = 0 ∧
      (Matrix.fromBlocks 0 (blockB m) (blockC m) 0).mulVec (radial1 m) = radial0 m := by
  classical
  let d : ℝ := 1 - (m : ℝ) ^ 2 / 2
  have hd : d ≠ 0 := neutral_denominator_ne_zero m
  have hS0 : (chargeMatrix m).mulVec (fun _ => (1 : ℝ)) = charge (2 * m) := by
    rw [chargeMatrix_diagonal]
    ext j
    simp [Matrix.mulVec_diagonal, charge]
  have hS1 : (chargeMatrix m).mulVec (fun j => charge (2 * m) j / d) =
      fun _ => d⁻¹ := by
    rw [chargeMatrix_diagonal]
    ext j
    rw [Matrix.mulVec_diagonal]
    change (-1 : ℝ) ^ (j.val + 2) * (charge (2 * m) j / d) = d⁻¹
    rw [← mul_div_assoc, show (-1 : ℝ) ^ (j.val + 2) = charge (2 * m) j by rfl,
      charge_square, one_div]
  have hB : (blockB m).mulVec (fun _ => (1 : ℝ)) = 0 := by
    rw [blockB, ← Matrix.mulVec_mulVec, hS0, Matrix.sub_mulVec]
    ext j
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [show (∑ k, weights m j k * charge (2 * m) k) =
        charge (2 * m) j * diagonalWeight m by
      simpa only [charge, mul_comm] using alternating_weight_sum_all m hm j]
    ring
  have hC : (blockC m).mulVec (fun j => charge (2 * m) j / d) = fun _ => 1 := by
    rw [blockC, ← Matrix.mulVec_mulVec, hS1, Matrix.sub_mulVec]
    ext j
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [← Finset.sum_mul, weight_sum_all m hm j]
    have hdiff : diagonalWeight m + 1 - (((2 * m : ℕ) : ℝ) ^ 2 - 1) / 12 = d := by
      simp only [diagonalWeight, d]
      ring
    calc
      _ = (diagonalWeight m + 1 - (((2 * m : ℕ) : ℝ) ^ 2 - 1) / 12) * d⁻¹ := by ring
      _ = 1 := by rw [hdiff, mul_inv_cancel₀ hd]
  have hz (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
      A.mulVec (fun _ => 0) = 0 := by
    ext j
    simp [Matrix.mulVec, dotProduct]
  constructor
  · rw [Matrix.fromBlocks_mulVec]
    ext p
    cases p <;> simp [radial0, hB, hz]
  · rw [Matrix.fromBlocks_mulVec]
    change Sum.elim _ _ = _
    ext p
    cases p <;> simp [radial1, radial0, hC, d, hz]

/-- The exact real Cartesian chain corresponding to v0=(0,1), v1=(s/d,0). -/
theorem cartesian_chain (m : ℕ) (hm : 1 ≤ m) :
    realOperator m (cartesian0 m) = 0 ∧
      realOperator m (cartesian1 m) = cartesian0 m := by
  let R := AlternatingPolygonSpectrum.rotation (2 * m)
  let J := jacobian (2 * m)
  let M := Matrix.fromBlocks 0 (blockB m) (blockC m) 0
  have hJR : J * R = R * M := by
    have h := congrArg (fun A => R * A) (rotated_jacobian_all m hm)
    dsimp only [R, J, M] at h ⊢
    simpa only [← Matrix.mul_assoc, rotation_mul_transpose, Matrix.one_mul] using h
  constructor
  · change J.mulVec (R.mulVec (radial0 m)) = 0
    rw [Matrix.mulVec_mulVec, hJR, ← Matrix.mulVec_mulVec,
      (block_radial_chain m hm).1, Matrix.mulVec_zero]
  · change J.mulVec (R.mulVec (radial1 m)) = R.mulVec (radial0 m)
    rw [Matrix.mulVec_mulVec, hJR, ← Matrix.mulVec_mulVec, (block_radial_chain m hm).2]

theorem cartesian0_ne_zero (m : ℕ) (hm : 1 ≤ m) : cartesian0 m ≠ 0 := by
  intro h
  have hz : radial0 m = 0 := by
    have h' := congrArg (AlternatingPolygonSpectrum.rotation (2 * m)).transpose.mulVec h
    simpa only [cartesian0, Matrix.mulVec_mulVec,
      mul_eq_one_comm.mp (rotation_mul_transpose (2 * m)),
      Matrix.one_mulVec, Matrix.mulVec_zero] using h'
  have hcoord := congrFun hz (.inr ⟨0, by omega⟩)
  norm_num [radial0] at hcoord

/-- The complete real linearized flow has an unbounded orbit, even in the dipole and square. -/
theorem unbounded_linear_drift (m : ℕ) (hm : 1 ≤ m) :
    (∀ t : ℝ, HasDerivAt (fun τ : ℝ => cartesian1 m + τ • cartesian0 m)
      (realOperator m (cartesian1 m + t • cartesian0 m)) t) ∧
      ¬ Bornology.IsBounded (Set.range (fun t : ℝ => cartesian1 m + t • cartesian0 m)) := by
  constructor
  · intro t
    have hA : realOperator m (cartesian1 m + t • cartesian0 m) = cartesian0 m := by
      rw [map_add, map_smul, (cartesian_chain m hm).1, (cartesian_chain m hm).2,
        smul_zero, add_zero]
    rw [hA]
    simpa using ((hasDerivAt_id t).smul_const (cartesian0 m)).const_add (cartesian1 m)
  · intro h
    obtain ⟨C, hC, hbound⟩ := h.exists_pos_norm_le
    have hn : 0 < ‖cartesian0 m‖ := norm_pos_iff.mpr (cartesian0_ne_zero m hm)
    let t : ℝ := (C + ‖cartesian1 m‖ + 1) / ‖cartesian0 m‖
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hb := hbound _ (Set.mem_range_self t)
    have htri := norm_sub_le (cartesian1 m + t • cartesian0 m) (cartesian1 m)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at htri
    have he : t * ‖cartesian0 m‖ = C + ‖cartesian1 m‖ + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hn)
    linarith

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
