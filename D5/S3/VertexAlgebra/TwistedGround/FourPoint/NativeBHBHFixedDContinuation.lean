/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHBHFixedDContinuation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed D on the BHBH right radial domain by finite reversal. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedProductRadialInversion

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHFixedDContinuation

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedUpperRightSkew (rightField_odd_zero)
open NativeHBHBCanonicalContinuation (upperRightDomain hbhbUpperAmplitude hbhbUpperAmplitude_hasSum_d)
open NativeBHBHCanonicalContinuation (outerRoot innerRoot bhbhUpperAmplitude)
open NativeFixedCrossedProductToIterate (dJointTerm)
open NativeFixedProductRadialInversion (fixedProductReversalWeight fixed_d_joint_hasSum_detector_reversal)

open private reversal_roots root_norm_order weight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation
open private dMode dMode_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBCanonicalContinuation
open private grade_mod_two from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

private theorem hbhb_fixed_d_tsum_neg_root (u v : TwistedEven) (w b : TwistedOdd)
    (x z : ℂ) :
    (∑' p, dJointTerm false true u v w b x (-z) p) =
      ∑' p, dJointTerm false true u v w b x z p := by
  apply tsum_congr
  intro p
  by_cases hp : Even p.2
  · simp only [dJointTerm, hp.neg_zpow]
  · simp [dJointTerm, rightField_odd_zero ℒ leechUnit true p.2 (Int.not_even_iff_odd.mp hp)]

private theorem phase (M K : ℕ) (h : Odd ((K : ℤ) - M)) :
    I ^ ((K : ℤ) - M) = -(I ^ ((M : ℤ) - K)) := by
  have he : (K : ℤ) - M = ((M : ℤ) - K) + 2 * ((K : ℤ) - M) := by ring
  calc
    I ^ ((K : ℤ) - M) = I ^ ((M : ℤ) - K) * (I ^ (2 : ℤ)) ^ ((K : ℤ) - M) := by
      rw [← zpow_mul, ← zpow_add₀ Complex.I_ne_zero, ← he]
    _ = -(I ^ ((M : ℤ) - K)) := by
      rw [zpow_ofNat, Complex.I_sq, h.neg_zpow, one_zpow, mul_neg, mul_one]

/-- For actual homogeneous states the literal BHBH fixed D product sums
to the same reciprocal amplitude on the entire upper right domain. -/
theorem bhbhUpperAmplitude_hasSum_d (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperRightDomain) :
    HasSum (dJointTerm true false P R Q S (outerRoot y) (innerRoot y))
      (bhbhUpperAmplitude M K P R Q S y) := by
  let X := outerRoot y
  let Z := innerRoot y
  let U (i j : ℕ) := hbhbUpperAmplitude ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R y
  obtain ⟨hX, hZ, _, hx', hz', _, _⟩ := reversal_roots hy.1
  have hD := fixed_d_joint_hasSum_detector_reversal true false M K H J P R Q S
    hP hQ hR hS (xR := X) (zR := Z) hX hZ ((root_norm_order hy.1).2 hy.2)
  change Z⁻¹ = Complex.sqrt (1 - y) at hx'
  change X⁻¹ = -(I * Complex.sqrt y) at hz'
  rw [hx', hz'] at hD
  have hval (i j : ℕ) :
      fixedProductReversalWeight K M Z X j i *
        (∑' k, dJointTerm false true ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R
          (Complex.sqrt (1 - y)) (-(I * Complex.sqrt y)) k) = weight M K y i j * U i j := by
    rw [hbhb_fixed_d_tsum_neg_root, (hbhbUpperAmplitude_hasSum_d _ _ _ _ hy).tsum_eq]
    unfold fixedProductReversalWeight weight X Z U
    ring
  have htotal :
      (∑ j ∈ Finset.range (K / 2 + 1), ∑ i ∈ Finset.range (M / 2 + 1),
        fixedProductReversalWeight K M Z X j i *
          (∑' k, dJointTerm false true ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R
            (Complex.sqrt (1 - y)) (-(I * Complex.sqrt y)) k)) =
      ∑ i ∈ Finset.range (M / 2 + 1), ∑ j ∈ Finset.range (K / 2 + 1),
        weight M K y i j * U i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hval i j
  rw [htotal] at hD
  refine Eq.mp (congrArg (HasSum (dJointTerm true false P R Q S X Z)) ?_) hD
  by_cases hzero : P = 0 ∨ Q = 0
  · have hU (i j : ℕ) : U i j = 0 := by
      refine (hbhbUpperAmplitude_hasSum_d _ _ _ _ hy).unique (hasSum_zero.congr_fun ?_)
      intro k
      have hzmode : dMode LinearMap.id y k ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R = 0 := by
        rcases hzero with h | h <;> simp [h]
      simpa only [dMode_apply, LinearMap.id_apply] using hzmode
    change I ^ ((K : ℤ) - M) * (∑ i ∈ Finset.range (M / 2 + 1),
      ∑ j ∈ Finset.range (K / 2 + 1), weight M K y i j * U i j) =
      -(I ^ ((M : ℤ) - K) * (∑ i ∈ Finset.range (M / 2 + 1),
        ∑ j ∈ Finset.range (K / 2 + 1), weight M K y i j * U i j))
    simp [hU]
  · push Not at hzero
    have hMp : M % 2 = 1 := grade_mod_two (s := true) (u := P) hP hzero.1
    have hKp : K % 2 = 0 := grade_mod_two (s := false) (u := Q) hQ hzero.2
    have hp : Odd ((K : ℤ) - M) := Int.odd_iff.mpr (by omega)
    rw [phase M K hp, neg_mul]
    rfl

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHFixedDContinuation
