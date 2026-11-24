/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedCrossedProductToIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedCrossedProductToIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native mixed D double series sums to the transposed A iterate with finite detector translation. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedCrossedProductToIterate

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit field_even_zero field_coeff)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeOddUpperRightSkew
  (lowering rightField rightField_coeff rightField_even_zero R_pairing_finite)
open NativeMixedAIterateRadial (aJointTerm mixed_a_joint_summable_of_homogeneous)
open NativeMixedUpperProductCusp (bJointTerm)

open private J_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

private def shiftOuterMode (ell : ℕ) : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
  (Equiv.refl ℤ).prodCongr (Equiv.subRight (2 * (ell : ℤ)))

private theorem bJointTerm_eq_sum_shifted_aJointTerm (s t : Bool) (N : ℕ)
    (P : State s) (R : State (!s)) (Q : State t) (S : State (!t))
    (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hz : zR ≠ 0) (i : ℤ × ℤ) :
    bJointTerm s t P R Q S zR xR i =
      ∑ ell ∈ Finset.range (N / 2 + 1),
        (zR ^ (2 * ell) / (ell.factorial : ℂ)) *
          aJointTerm s P R Q.val ((L₁ (!t) ^ ell) S).val xR (I * zR) (shiftOuterMode ell i) := by
  rcases i with ⟨a, e⟩
  let c : OddCarrier ℒ := (mu s P).coeff a R
  simp only [bJointTerm, aJointTerm, shiftOuterMode, Equiv.prodCongr_apply,
    Equiv.refl_apply, Equiv.subRight_apply]
  change actualForm ℒ leechUnit S.val ((rightField ℒ leechUnit t Q).coeff e c).val *
      (xR ^ a * zR ^ e) =
    ∑ ell ∈ Finset.range (N / 2 + 1),
      (zR ^ (2 * ell) / (ell.factorial : ℂ)) *
        (actualForm ℒ leechUnit ((L₁ (!t) ^ ell) S).val
          ((correctedField ℒ leechUnit c.val).coeff (e - 2 * (ell : ℤ)) Q.val) *
            (xR ^ a * (I * zR) ^ (e - 2 * (ell : ℤ))))
  by_cases he : Even e
  · rw [rightField_even_zero ℒ leechUnit t e he Q c]
    simp only [Submodule.coe_zero, map_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ell _
    obtain ⟨k, hk⟩ := he
    have he' : Even (e - 2 * (ell : ℤ)) := ⟨k - (ell : ℤ), by omega⟩
    have hzero : (correctedField ℒ leechUnit c.val).coeff (e - 2 * (ell : ℤ)) Q.val = 0 := by
      simpa only [field_coeff, Submodule.coe_zero] using
        congrArg (fun v : State (!t) => v.val)
          (field_even_zero ℒ leechUnit t (e - 2 * (ell : ℤ)) he' c Q)
    rw [hzero, map_zero, zero_mul, mul_zero]
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
    let n : ℤ := -k - 2
    have heq : e = -2 * n - 3 := by dsimp only [n]; omega
    rw [heq, rightField_coeff ℒ leechUnit t n Q c,
      R_pairing_finite ℒ leechUnit t n N Q c S hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ell _
    have hmode :
        -2 * (n + (ell : ℤ)) - 3 = (-2 * n - 3) - 2 * (ell : ℤ) := by ring
    have hzpow :
        zR ^ (-2 * n - 3) = zR ^ (2 * ell) * zR ^ ((-2 * n - 3) - 2 * (ell : ℤ)) := by
      have hexp : ((2 * ell : ℕ) : ℤ) + ((-2 * n - 3) - 2 * (ell : ℤ)) =
          -2 * n - 3 := by
        push_cast
        ring
      rw [← zpow_natCast zR (2 * ell), ← zpow_add₀ hz, hexp]
    rw [J_val, ← lowering_pow_val ℒ leechUnit (!t) ell S, hmode, div_eq_mul_inv,
      mul_zpow, hzpow]
    ring

/-- The literal mixed D product in order `(P, R, Q, S)` sums to the mixed A
iterate with the translated detector. For `xR ^ 2 = x` and `zR ^ 2 = z`,
the transposed coordinates are `(x - z, -z)`. The A difference root is
`xR` and its upper outer root is `I * zR`. -/
theorem mixed_d_joint_hasSum_crossed_a (s t : Bool) (M L K N : ℕ)
    (P : State s) (R : State (!s)) (Q : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hR : R.val ∈ actualGrade ℒ leechUnit L)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖xR‖ < ‖zR‖) :
    HasSum (bJointTerm s t P R Q S zR xR)
      (∑ ell ∈ Finset.range (N / 2 + 1),
        (zR ^ (2 * ell) / (ell.factorial : ℂ)) *
          (∑' i, aJointTerm s P R Q.val ((L₁ (!t) ^ ell) S).val xR (I * zR) i)) := by
  have hrad : ‖xR‖ < ‖I * zR‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using hr
  have hsum (ell : ℕ) (hell : ell ∈ Finset.range (N / 2 + 1)) :
      HasSum
        (fun i => (zR ^ (2 * ell) / (ell.factorial : ℂ)) *
          aJointTerm s P R Q.val ((L₁ (!t) ^ ell) S).val xR (I * zR) (shiftOuterMode ell i))
        ((zR ^ (2 * ell) / (ell.factorial : ℂ)) *
          (∑' i, aJointTerm s P R Q.val ((L₁ (!t) ^ ell) S).val xR (I * zR) i)) := by
    have hell' : ell ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hell)
    have hdesc := lowered_grade (s := !t) (u := S) hS hell'
    have hA := (mixed_a_joint_summable_of_homogeneous s t M L K (N - 2 * ell)
      P R Q ((L₁ (!t) ^ ell) S) hP hR hQ hdesc hx hrad).hasSum
    exact ((shiftOuterMode ell).hasSum_iff.mpr hA).mul_left _
  exact (hasSum_sum (s := Finset.range (N / 2 + 1)) hsum).congr_fun
    (bJointTerm_eq_sum_shifted_aJointTerm s t N P R Q S hS hz)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedCrossedProductToIterate
