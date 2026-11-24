/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedIterateRadialInversion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedIterateRadialInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Radial convergence discharges summed native mixed A detector inversion. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm

/-! Restrict the convergent radial iterate to the selected detector modes and
remove their common Laurent monomial to obtain the energy series. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateRadialInversion

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeDetectorTranslation (detector_apply)
open Orbifold.NativeMixedPairSkew (swapInput)
open Orbifold.NativeMixedIterateInversionCoefficient (aCoeff)
open NativeMixedAIterateRadial (aJointTerm mixed_a_joint_summable_of_homogeneous)
open NativeMixedIterateInversionGerm (aCoeff_inversion_hasSum binomialExponent)
open private descend_grade swapped_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
open private exchangedCoeff factorials from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm

local notation "ℒ" => leechData
local notation "T" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev weight (M : ℕ) : ℤ := 3 + (M : ℤ)

private theorem aCoeff_summable (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    Summable (fun n : ℕ => aCoeff s t (weight M) (weight K) (weight H) (weight J) n
      P Q R S * ρ ^ n) := by
  by_cases hzero : ρ = 0
  · subst ρ
    exact (hasSum_single (f := fun n : ℕ =>
      aCoeff s t (weight M) (weight K) (weight H) (weight J) n P Q R S * (0 : ℂ) ^ n)
      0 (fun n hn => by rw [zero_pow hn, mul_zero])).summable
  let ξ : ℂ := ρ ^ (((2 : ℕ) : ℂ)⁻¹)
  have hsq : ξ ^ 2 = ρ := Complex.cpow_nat_inv_pow ρ (by decide : (2 : ℕ) ≠ 0)
  have hξ₀ : ξ ≠ 0 := by
    intro h
    apply hzero
    rw [← hsq, h, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hξ : ‖ξ‖ < ‖(1 : ℂ)‖ := by
    have h : ‖ξ‖ ^ 2 < 1 := by rwa [← norm_pow, hsq]
    rw [norm_one]
    by_contra! hle
    nlinarith
  let modes (n : ℕ) : ℤ × ℤ :=
    (2 * (n : ℤ) - weight M - weight K, weight J - weight H - 2 * (n : ℤ))
  have hmodes : Function.Injective modes := by
    intro n m h
    have hfirst := congrArg Prod.fst h
    dsimp only [modes] at hfirst
    omega
  have h := mixed_a_joint_summable_of_homogeneous s t M K H J P Q R S hP hQ hR hS hξ₀ hξ
  refine ((h.comp_injective hmodes).mul_left (ξ ^ (weight M + weight K))).congr ?_
  intro n
  have hpow : ξ ^ (weight M + weight K) *
      ξ ^ (2 * (n : ℤ) - weight M - weight K) = ρ ^ n := by
    rw [← zpow_add₀ hξ₀, show weight M + weight K +
      (2 * (n : ℤ) - weight M - weight K) = 2 * (n : ℤ) by ring,
      zpow_mul, zpow_ofNat, hsq, zpow_natCast]
  simp only [Function.comp_apply, aJointTerm, modes, one_zpow, mul_one, aCoeff, detector_apply]
  rw [(ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq S.val,
    mul_left_comm, hpow]

/-- The summed mixed A detector inversion on the unit disk, with the
exchanged descendant values supplied by their own native energy series. -/
theorem aCoeff_inversion_hasSum_unit_disk (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    HasSum (fun n : ℕ => aCoeff s t (weight M) (weight K) (weight H) (weight J) n
        P Q R S * ρ ^ n)
      (Complex.I ^ (weight M - weight K) *
        ∑ j ∈ Finset.range (K / 2 + 1), ∑ i ∈ Finset.range (M / 2 + 1),
          (factorials i j)⁻¹ * (ρ ^ (j + i) *
            ((1 + ρ) ^ binomialExponent (weight M) (weight K) (weight H) (weight J) j *
              ∑' n : ℕ, exchangedCoeff s t (weight M) (weight K) (weight H) (weight J)
                P Q R S j i n * ρ ^ n))) := by
  apply aCoeff_inversion_hasSum s t M K H J P Q R S hP hQ hR hS hρ
  intro j i hj hi
  have hj' : 2 * j ≤ K := by omega
  have hi' : 2 * i ≤ M := by omega
  have hw (L k : ℕ) (hk : 2 * k ≤ L) :
      weight (L - 2 * k) = weight L - 2 * (k : ℤ) := by
    dsimp [weight]
    omega
  have hdesc := aCoeff_summable (!s) (!t) (K - 2 * j) (M - 2 * i) J H
    ((T (!s) ^ j) Q) (swapInput ((T s ^ i) P)) S (swapInput R)
    (descend_grade hQ hj') (swapped_grade (descend_grade hP hi')) hS (swapped_grade hR) hρ
  simpa only [hw K j hj', hw M i hi', exchangedCoeff] using hdesc.hasSum

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateRadialInversion
