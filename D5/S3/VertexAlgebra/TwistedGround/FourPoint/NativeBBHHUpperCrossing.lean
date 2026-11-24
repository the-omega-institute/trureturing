/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBBHHUpperCrossing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual native Leech BBHH A and B sums on the physical upper lens. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHFixedDContinuation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23PhysicalRoots

/-! The native BBHH B product continues the signed, transported BHBH B product.
The BHBH fixed D product gives the BBHH A iterate on the upper lens. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Topology
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHUpperCrossing

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeMixedPairSkew (swapInput)
open NativeHBHBCanonicalContinuation (upperRightDomain)
open NativeBHBHCanonicalContinuation
  (outerRoot outerRoot_eq innerRoot bhbhUpperAmplitude bhbhUpperAmplitude_analytic
    bhbhUpperAmplitude_hasSum_ab)
open NativeBHBHFixedDContinuation (bhbhUpperAmplitude_hasSum_d)
open NativeMixedBProductUpperDisk
  (upperUnitDisk isPreconnected_upperUnitDisk physicalOuterRoot physicalInnerRoot
    physical_root_ratio b_joint_product_analytic_physical_translated)
open NativeMixedUpperProductCusp (bJointTerm)
open NativeMixedProductSlot23PhysicalRoots (b_joint_product_hasSum_slot23_physical b_joint_product_hasSum_scale)
open NativeFixedCrossedProductToIterate
  (aJointTerm translatedDetector translationWeight fixed_a_joint_summable_of_homogeneous
    fixed_d_joint_hasSum_crossed_a)

open private source_roots reversal_roots root_norm_order from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation
open private sqrt_re_pos_of_im_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHDetectorReversal
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private grade_mod_two bModeLinear bModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private lowered_grade cancel_lowering_orders from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private aModeLinear aModeLinear_apply fixed_a_off_diagonal from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private BasisIndex basis from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private isOpen_upperUnitDisk basisComponent basisComponent_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

private def relativeParameter (y : ℂ) : ℂ := y / (y - 1)

private theorem one_sub_ne_zero {y : ℂ} (hy : 0 < y.im) : 1 - y ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

private theorem relativeParameter_ne_zero {y : ℂ} (hy : 0 < y.im) :
    relativeParameter y ≠ 0 := by
  apply div_ne_zero
  · exact ne_of_apply_ne Complex.im (by simpa using hy.ne')
  · rw [← neg_sub]
    exact neg_ne_zero.mpr (one_sub_ne_zero hy)

private theorem physical_roots (y : ℂ) :
    outerRoot y * innerRoot y = physicalOuterRoot y ∧
      I * innerRoot y = physicalInnerRoot y := by
  constructor
  · simp only [outerRoot_eq, innerRoot, physicalOuterRoot, div_eq_mul_inv, mul_inv_rev]
    rw [mul_comm (Complex.sqrt (1 - y))⁻¹ (Complex.sqrt y)⁻¹, mul_assoc]
  · simp only [innerRoot, physicalInnerRoot, div_eq_mul_inv]

/-- Dividing the physical triple by its first root gives the principal BBHH roots. -/
theorem normalized_physical_roots {y : ℂ} (hy : y ∈ upperUnitDisk) :
    let X := outerRoot y
    let Z := innerRoot y
    let D := X * Z
    D / D = 1 ∧ I * Z / D = Complex.sqrt y ∧ X / D = Complex.sqrt (1 - y) := by
  dsimp only
  obtain ⟨hx, hz, hD, hinv, _, _, _⟩ := reversal_roots hy.2
  refine ⟨hD, ?_, ?_⟩
  · rw [(physical_roots y).1, (physical_roots y).2]
    exact physical_root_ratio hy
  · rw [div_mul_eq_div_div, div_self hx, one_div, hinv]

private theorem relative_roots {y : ℂ} (hy : 0 < y.im) :
    let X := outerRoot y
    let Z := innerRoot y
    (Z / X) ^ (2 : ℕ) = relativeParameter y ∧
      (X * Z) / X = Complex.sqrt (1 - relativeParameter y) := by
  dsimp only
  obtain ⟨hx, _, _, _, _, _, _⟩ := reversal_roots hy
  obtain ⟨_, _, _, hcyS⟩ := source_roots hy
  have hy₀ := one_sub_ne_zero hy
  have hsq : innerRoot y ^ (2 : ℕ) = (1 - y)⁻¹ := by
    rw [innerRoot, inv_pow, sqrt_square]
  have hv' : 1 - relativeParameter y = (1 - y)⁻¹ := by
    rw [relativeParameter, show y - 1 = -(1 - y) by ring, div_neg]
    field_simp [hy₀]
    ring
  constructor
  · rw [outerRoot_eq, div_pow, hsq, div_pow, Complex.I_sq, sqrt_square, relativeParameter,
      show y - 1 = -(1 - y) by ring]
    field_simp [hy₀, show y ≠ 0 from ne_of_apply_ne Complex.im (by simpa using hy.ne')]
  · rw [mul_comm, mul_div_cancel_right₀ _ hx]
    have hZ : 0 < (innerRoot y).re := by
      rw [innerRoot, Complex.inv_re]
      apply div_pos
      · apply sqrt_re_pos_of_im_ne_zero
        simpa using hy.ne'
      · exact Complex.normSq_pos.mpr hcyS
    have hroot : 0 < (Complex.sqrt (1 - relativeParameter y)).re := by
      apply sqrt_re_pos_of_im_ne_zero
      rw [hv', Complex.inv_im]
      exact div_ne_zero (by simpa using hy.ne') (Complex.normSq_pos.mpr hy₀).ne'
    have hSquare : innerRoot y ^ (2 : ℕ) = Complex.sqrt (1 - relativeParameter y) ^ (2 : ℕ) := by
      rw [hsq, sqrt_square, hv']
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hSquare with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      linarith

private theorem patch_left {y : ℂ} (hy : 0 < y.im)
    (hv : ‖relativeParameter y‖ < 1 / 2) : y.re < (1 / 2 : ℝ) := by
  have hpos := norm_pos_iff.mpr (one_sub_ne_zero hy)
  have h : ‖y‖ < ‖1 - y‖ := by
    rw [relativeParameter, norm_div, show y - 1 = -(1 - y) by ring, norm_neg] at hv
    apply (div_lt_one hpos).mp
    linarith
  have hre := (norm_one_sub_lt_iff (1 - y)).mp (by rwa [sub_sub_cancel])
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith

private theorem local_slot23 (M K H J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperUnitDisk) (hv : ‖relativeParameter y‖ < 1 / 2) :
    HasSum (bJointTerm true true R Q P (translatedDetector false J (innerRoot y ^ 2) S)
      (physicalOuterRoot y) (physicalInnerRoot y)) (-bhbhUpperAmplitude M K P R Q S y) := by
  have hB := (bhbhUpperAmplitude_hasSum_ab M K H J P R Q S hP hQ hR hS hy.2).2
    (patch_left hy.2 hv)
  by_cases hzero : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0
  · have hSzero : translatedDetector false J (innerRoot y ^ 2) (0 : TwistedEven) = 0 := by
      simp [translatedDetector]
    have hG : bhbhUpperAmplitude M K P R Q S y = 0 := by
      apply hB.unique
      refine hasSum_zero.congr_fun fun i => ?_
      rcases hzero with h | h | h | h <;> simp [← bModeLinear_apply, h]
    rw [hG, neg_zero]
    refine hasSum_zero.congr_fun fun i => ?_
    rcases hzero with h | h | h | h <;> simp [← bModeLinear_apply, h, hSzero]
  push Not at hzero
  have hm := grade_mod_two hP hzero.1
  have hk := grade_mod_two hQ hzero.2.1
  have hh := grade_mod_two hR hzero.2.2.1
  have hj := grade_mod_two hS hzero.2.2.2
  have hKH : Odd ((K : ℤ) + H) := Int.odd_iff.mpr (by simp at hk hh; omega)
  have hJM : Odd ((J : ℤ) - M) := Int.odd_iff.mpr (by simp at hj hm; omega)
  obtain ⟨hx, _, _, _, _, _, _⟩ := reversal_roots hy.2
  obtain ⟨hvSq, hD⟩ := relative_roots hy.2
  obtain ⟨hSource, hTarget⟩ :=
    b_joint_product_hasSum_slot23_physical false true M K H J Q R P S
      hQ hR hP hS hKH hJM hx hvSq (norm_pos_iff.mpr (relativeParameter_ne_zero hy.2)) hv hD
  have hphase : (-1 : ℂ) ^ (3 + K) = -1 := by
    apply Odd.neg_one_pow
    exact Nat.odd_iff.mpr (by simp at hk; omega)
  rw [hphase, neg_one_mul] at hSource
  have hValue := congrArg Neg.neg (hB.unique hSource)
  rw [neg_neg] at hValue
  have hswap : swapInput (s := false) Q = Q := Subtype.ext rfl
  rw [← hValue] at hTarget
  change HasSum (bJointTerm true true R (swapInput (s := false) Q) P
    (∑ j ∈ Finset.range (J / 2 + 1),
      ((innerRoot y ^ 2) ^ j / (j.factorial : ℂ)) • (L₁ false ^ j) S)
    (outerRoot y * innerRoot y) (I * innerRoot y)) _ at hTarget
  simpa only [hswap, translatedDetector, translationWeight, div_eq_mul_inv,
    (physical_roots y).1, (physical_roots y).2] using hTarget

set_option maxHeartbeats 1200000 in
/-- The transported actual native BBHH B product has value -G throughout the upper disk. -/
theorem bbhh_b_hasSum_translated (M K H J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperUnitDisk) :
    HasSum (bJointTerm true true R Q P (translatedDetector false J (innerRoot y ^ 2) S)
      (physicalOuterRoot y) (physicalInnerRoot y)) (-bhbhUpperAmplitude M K P R Q S y) := by
  let T (u : ℂ) : TwistedEven :=
    ∑ j ∈ Finset.range (J / 2 + 1),
      (((1 / Complex.sqrt (1 - u)) ^ (2 : ℕ)) ^ j / (j.factorial : ℂ)) • (L₁ (!true) ^ j) S
  let b (u : ℂ) := bJointTerm true true R Q P (T u) (physicalOuterRoot u) (physicalInnerRoot u)
  let B (u : ℂ) := ∑' i, b u i
  have hB : AnalyticOnNhd ℂ B upperUnitDisk ∧
      ∀ u ∈ upperUnitDisk, HasSum (b u) (B u) :=
    b_joint_product_analytic_physical_translated true true J R Q P S
  have hT (u : ℂ) : T u = translatedDetector false J (innerRoot u ^ 2) S := by
    unfold T translatedDetector translationWeight innerRoot
    simp only [div_eq_mul_inv, one_mul]
    rfl
  have hSum (u : ℂ) (hu : u ∈ upperUnitDisk) :
      HasSum (bJointTerm true true R Q P (translatedDetector false J (innerRoot u ^ 2) S)
        (physicalOuterRoot u) (physicalInnerRoot u)) (B u) := by
    have h := hB.2 u hu
    change HasSum (bJointTerm true true R Q P (T u)
      (physicalOuterRoot u) (physicalInnerRoot u)) (B u) at h
    rwa [hT] at h
  have hG : AnalyticOnNhd ℂ (fun u => -bhbhUpperAmplitude M K P R Q S u) upperUnitDisk :=
    ((bhbhUpperAmplitude_analytic M K P R Q S).mono (fun _ hu => hu.2)).neg
  let y₀ : ℂ := (1 / 4 : ℝ) • I
  have hN : ‖y₀‖ = 1 / 4 := by
    change ‖(1 / 4 : ℝ) • I‖ = _
    norm_num [norm_smul, Real.norm_eq_abs]
  have hIm : 0 < y₀.im := by norm_num [y₀, Complex.smul_im, smul_eq_mul]
  have h₀ : y₀ ∈ upperUnitDisk := ⟨mem_ball_zero_iff.mpr (by rw [hN]; norm_num), hIm⟩
  have hden : 1 ≤ ‖y₀ - 1‖ := by
    simpa [y₀, Complex.smul_re, smul_eq_mul] using Complex.abs_re_le_norm (y₀ - 1)
  have hv₀ : ‖relativeParameter y₀‖ < 1 / 2 := by
    rw [relativeParameter, norm_div, hN, div_lt_iff₀ (by linarith : 0 < ‖y₀ - 1‖)]
    linarith
  have hc : ContinuousAt relativeParameter y₀ := by
    apply continuousAt_id.div (continuousAt_id.sub continuousAt_const)
    exact norm_pos_iff.mp (by linarith : 0 < ‖y₀ - 1‖)
  have hDisk : ∀ᶠ u in 𝓝 y₀, u ∈ upperUnitDisk := isOpen_upperUnitDisk.mem_nhds h₀
  have hSmall : ∀ᶠ u in 𝓝 y₀, ‖relativeParameter u‖ < 1 / 2 :=
    hc.norm (gt_mem_nhds hv₀)
  have hPatch : ∀ᶠ u in 𝓝 y₀, u ∈ upperUnitDisk ∧ ‖relativeParameter u‖ < 1 / 2 :=
    Filter.Eventually.and hDisk hSmall
  have hEq : B =ᶠ[𝓝 y₀] (fun u => -bhbhUpperAmplitude M K P R Q S u) := by
    filter_upwards [hPatch] with u hu
    exact (hSum u hu.1).unique (local_slot23 M K H J P R Q S hP hQ hR hS hu.1 hu.2)
  have he := hB.1.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_upperUnitDisk h₀ hEq hy
  change B y = -bhbhUpperAmplitude M K P R Q S y at he
  rw [← he]
  exact hSum y hy

/-- Actual homogeneous BBHH A and B double series on the upper unit lens.
The detector in both series is the same finite translation by the square of Z. -/
theorem bbhh_actual_upper_crossing_translated (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperUnitDisk) (hre : (1 / 2 : ℝ) < y.re) :
    let X := outerRoot y
    let Z := innerRoot y
    let T := translatedDetector false J (Z ^ 2) S
    HasSum (aJointTerm true false P R Q T X (I * Z)) (bhbhUpperAmplitude M K P R Q S y) ∧
      HasSum (bJointTerm true true R Q P T (X * Z) (I * Z)) (-bhbhUpperAmplitude M K P R Q S y) := by
  dsimp only
  have hB := bbhh_b_hasSum_translated M K H J P R Q S hP hQ hR hS hy
  rw [← (physical_roots y).1, ← (physical_roots y).2] at hB
  refine ⟨?_, hB⟩
  let X := outerRoot y
  let Z := innerRoot y
  obtain ⟨hx, hz, _, _, _, _, _⟩ := reversal_roots hy.2
  have hrad := (root_norm_order hy.2).2 hre
  have hD := bhbhUpperAmplitude_hasSum_d M K H J P R Q S hP hQ hR hS
    (show y ∈ upperRightDomain from ⟨hy.2, hre⟩)
  have hCross := fixed_d_joint_hasSum_crossed_a true false M H K J P R Q S
    hP hR hQ hS hx hz hrad
  have hA (j : ℕ) (hj : j ∈ Finset.range (J / 2 + 1)) :
      Summable (aJointTerm true false P R Q ((L₁ false ^ j) S) X (I * Z)) := by
    have hgrade := lowered_grade hS (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    exact fixed_a_joint_summable_of_homogeneous true false M H K (J - 2 * j)
      P R Q _ hP hR hQ hgrade hx (by simpa only [norm_mul, Complex.norm_I, one_mul] using hrad)
  have hSum := hasSum_sum (s := Finset.range (J / 2 + 1)) fun j hj =>
    (hA j hj).hasSum.mul_left (translationWeight (Z ^ 2) j)
  have hVal := hCross.unique hD
  change HasSum (aJointTerm true false P R Q (translatedDetector false J (Z ^ 2) S) X (I * Z)) (bhbhUpperAmplitude M K P R Q S y)
  rw [← hVal]
  refine hSum.congr_fun fun i => ?_
  simp only [← aModeLinear_apply, translatedDetector, map_sum, map_smul, smul_eq_mul]

private theorem eval_translation_inverse (f : TwistedEven →ₗ[ℂ] ℂ) (x : ℂ)
    (J : ℕ) (S : TwistedEven) :
    (∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-x) j *
      f (translatedDetector false (J - 2 * j) x ((L₁ false ^ j) S))) = f S := by
  let g (r : ℕ) := x ^ r * f ((L₁ false ^ r) S)
  have hzero : g 0 = f S := by simp [g, Module.End.one_apply]
  rw [← hzero, ← cancel_lowering_orders (J / 2) g]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hdegree : (J - 2 * j) / 2 = J / 2 - j := by
    have := Finset.mem_range.mp hj
    omega
  rw [translatedDetector, hdegree, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [map_smul, smul_eq_mul]
  rw [← Module.End.mul_apply, ← pow_add, add_comm q j]
  simp only [g, translationWeight, pow_add x j q]
  have hx : (-x) ^ j = (-1 : ℂ) ^ j * x ^ j := by rw [← mul_pow, neg_one_mul]
  rw [hx]
  ring

/-- The finite opposite translation removes the detector shift in both actual BBHH sums. -/
theorem bbhh_actual_upper_crossing_of_homogeneous (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperUnitDisk) (hre : (1 / 2 : ℝ) < y.re) :
    let X := outerRoot y
    let Z := innerRoot y
    let C := ∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(Z ^ 2)) j *
      bhbhUpperAmplitude M K P R Q ((L₁ false ^ j) S) y
    HasSum (aJointTerm true false P R Q S X (I * Z)) C ∧
      HasSum (bJointTerm true true R Q P S (X * Z) (I * Z)) (-C) := by
  let X := outerRoot y
  let Z := innerRoot y
  have h (j : ℕ) (hj : j ∈ Finset.range (J / 2 + 1)) :=
    bbhh_actual_upper_crossing_translated M K H (J - 2 * j) P R Q ((L₁ false ^ j) S)
      hP hQ hR (lowered_grade hS (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) hy hre
  dsimp only
  constructor
  · refine (hasSum_sum (s := Finset.range (J / 2 + 1)) fun j hj =>
      (h j hj).1.mul_left (translationWeight (-(Z ^ 2)) j)).congr_fun fun i => ?_
    simpa only [aModeLinear_apply] using
      (eval_translation_inverse (aModeLinear true false X (I * Z) i P R Q) (Z ^ 2) J S).symm
  · have hSum := hasSum_sum (s := Finset.range (J / 2 + 1)) fun j hj =>
      (h j hj).2.mul_left (translationWeight (-(Z ^ 2)) j)
    simp only [mul_neg, Finset.sum_neg_distrib] at hSum
    refine hSum.congr_fun fun i => ?_
    simp only [← bModeLinear_apply]
    exact (eval_translation_inverse (bModeLinear true true (X * Z) (I * Z) i R Q P) (Z ^ 2) J S).symm


private theorem bbhh_hasSum_scaled (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y c : ℂ} (hy : y ∈ upperUnitDisk) (hre : (1 / 2 : ℝ) < y.re) (hc : c ≠ 0) :
    let X := outerRoot y
    let Z := innerRoot y
    ∃ C : ℂ, HasSum (aJointTerm true false P R Q S (c * X) (c * (I * Z))) C ∧
      HasSum (bJointTerm true true R Q P S (c * (X * Z)) (c * (I * Z))) (-C) := by
  dsimp only
  by_cases hzero : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0
  · refine ⟨0, ?_, ?_⟩
    · refine hasSum_zero.congr_fun fun i => ?_
      rcases hzero with h | h | h | h <;> simp [← aModeLinear_apply, h]
    · rw [neg_zero]
      refine hasSum_zero.congr_fun fun i => ?_
      rcases hzero with h | h | h | h <;> simp [← bModeLinear_apply, h]
  push Not at hzero
  have hm := grade_mod_two hP hzero.1
  have hk := grade_mod_two hQ hzero.2.1
  have hh := grade_mod_two hR hzero.2.2.1
  have hMH : Even ((M : ℤ) + H) := Int.even_iff.mpr (by simp at hm hh; omega)
  have hHK : Odd ((H : ℤ) + K) := Int.odd_iff.mpr (by simp at hk hh; omega)
  let X := outerRoot y
  let Z := innerRoot y
  let e : ℤ := (J : ℤ) - M - (6 + (H : ℤ) + K)
  obtain ⟨hA, hB⟩ :=
    bbhh_actual_upper_crossing_of_homogeneous M K H J P R Q S hP hQ hR hS hy hre
  let C := ∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(Z ^ 2)) j *
    bhbhUpperAmplitude M K P R Q ((L₁ false ^ j) S) y
  refine ⟨c ^ e * C, ?_, ?_⟩
  · refine (hA.mul_left (c ^ e)).congr_fun fun i => ?_
    rcases i with ⟨m, n⟩
    by_cases hdiag : n = (J : ℤ) - K - (m + ((M : ℤ) + H + 6))
    · have htotal : m + n = e := by rw [hdiag]; dsimp [e]; ring
      simp only [aJointTerm, mul_zpow]
      rw [← htotal, zpow_add₀ hc]
      ring
    · simp only [aJointTerm, fixed_a_off_diagonal true false M H K J P R Q S
        hP hR hQ hS hMH m n hdiag, zero_mul, mul_zero]
  · simpa only [mul_neg] using b_joint_product_hasSum_scale true true M H K J R Q P S
      hR hQ hP hS hHK hc hB

set_option maxHeartbeats 1800000 in
/-- The actual BBHH sums at every nonzero common root scale for arbitrary Leech states. -/
theorem bbhh_actual_upper_crossing_scaled (P R : TwistedOdd) (Q S : TwistedEven)
    {y scale : ℂ} (hy : y ∈ upperUnitDisk) (hre : (1 / 2 : ℝ) < y.re)
    (hscale : scale ≠ 0) :
    let X := outerRoot y
    let Z := innerRoot y
    ∃ C : ℂ, HasSum (aJointTerm true false P R Q S (scale * X) (scale * (I * Z))) C ∧
      HasSum (bJointTerm true true R Q P S (scale * (X * Z)) (scale * (I * Z))) (-C) := by
  classical
  let X := outerRoot y
  let Z := innerRoot y
  let ps := (basis.repr P.val).support
  let rs := (basis.repr R.val).support
  let qs := (basis.repr Q.val).support
  let ss := (basis.repr S.val).support
  let p := basisComponent true P
  let r := basisComponent true R
  let q := basisComponent false Q
  let s := basisComponent false S
  let g (c b a d : BasisIndex) :=
    ∑' i, aJointTerm true false (p a) (r c) (q b) (s d) (scale * X) (scale * (I * Z)) i
  have h (c b a d : BasisIndex) :
      HasSum (aJointTerm true false (p a) (r c) (q b) (s d) (scale * X) (scale * (I * Z))) (g c b a d) ∧
      HasSum (bJointTerm true true (r c) (q b) (p a) (s d) (scale * (X * Z)) (scale * (I * Z))) (-g c b a d) := by
    obtain ⟨C, hA, hB⟩ := bbhh_hasSum_scaled
      (oddWeight ℒ a.1) (oddWeight ℒ b.1) (oddWeight ℒ c.1) (oddWeight ℒ d.1)
      (p a) (r c) (q b) (s d) (basisComponent_grade true P a) (basisComponent_grade false Q b)
      (basisComponent_grade true R c) (basisComponent_grade false S d) hy hre hscale
    have he : g c b a d = _ := hA.tsum_eq
    exact ⟨hA.summable.hasSum, he.symm ▸ hB⟩
  refine ⟨∑ c ∈ rs, ∑ b ∈ qs, ∑ a ∈ ps, ∑ d ∈ ss, g c b a d, ?_, ?_⟩
  · refine (hasSum_sum (s := rs) fun c _ => hasSum_sum (s := qs) fun b _ =>
      hasSum_sum (s := ps) fun a _ => hasSum_sum (s := ss) fun d _ => (h c b a d).1).congr_fun
        fun i => ?_
    simp only [← aModeLinear_apply]
    conv_lhs =>
      rw [← sum_projectedBasis true P]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis true R]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false Q]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false S]
      simp only [map_sum]
    exact Finset.sum_comm_cycle.symm
  · have hB := hasSum_sum (s := rs) fun c _ => hasSum_sum (s := qs) fun b _ =>
      hasSum_sum (s := ps) fun a _ => hasSum_sum (s := ss) fun d _ => (h c b a d).2
    simp only [Finset.sum_neg_distrib] at hB
    refine hB.congr_fun fun i => ?_
    simp only [← bModeLinear_apply]
    conv_lhs =>
      rw [← sum_projectedBasis true R]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false Q]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis true P]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false S]
      simp only [map_sum]


/-- The actual BBHH sums at the inherited physical roots for arbitrary Leech states. -/
theorem bbhh_actual_upper_crossing (P R : TwistedOdd) (Q S : TwistedEven)
    {y : ℂ} (hy : y ∈ upperUnitDisk) (hre : (1 / 2 : ℝ) < y.re) :
    let X := outerRoot y
    let Z := innerRoot y
    ∃ C : ℂ, HasSum (aJointTerm true false P R Q S X (I * Z)) C ∧
      HasSum (bJointTerm true true R Q P S (X * Z) (I * Z)) (-C) := by
  simpa only [one_mul] using
    bbhh_actual_upper_crossing_scaled P R Q S hy hre (scale := 1) one_ne_zero

/-- Arbitrary-state BBHH sewing at the principal normalized roots. -/
theorem bbhh_actual_upper_crossing_normalized (P R : TwistedOdd) (Q S : TwistedEven)
    {y : ℂ} (hy : y ∈ upperUnitDisk) (hre : (1 / 2 : ℝ) < y.re) :
    ∃ C : ℂ, HasSum (aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y)) C ∧
      HasSum (bJointTerm true true R Q P S 1 (Complex.sqrt y)) (-C) := by
  let X := outerRoot y
  let Z := innerRoot y
  let D := X * Z
  obtain ⟨hx, hz, _, _, _, _, _⟩ := reversal_roots hy.2
  obtain ⟨hD, hinner, hsep⟩ := normalized_physical_roots hy
  obtain ⟨C, hA, hB⟩ := bbhh_actual_upper_crossing_scaled P R Q S hy hre
    (scale := D⁻¹) (inv_ne_zero (mul_ne_zero hx hz))
  have hOuter : D⁻¹ * (X * Z) = 1 := by simpa only [D, div_eq_mul_inv, mul_comm] using hD
  have hInner : D⁻¹ * (I * Z) = Complex.sqrt y := by
    simpa only [D, X, Z, div_eq_mul_inv, mul_comm] using hinner
  have hSep : D⁻¹ * X = Complex.sqrt (1 - y) := by
    simpa only [D, X, Z, div_eq_mul_inv, mul_comm] using hsep
  change HasSum (aJointTerm true false P R Q S (D⁻¹ * X) (D⁻¹ * (I * Z))) C at hA
  change HasSum (bJointTerm true true R Q P S (D⁻¹ * (X * Z)) (D⁻¹ * (I * Z))) (-C) at hB
  rw [hSep, hInner] at hA
  rw [hOuter, hInner] at hB
  exact ⟨C, hA, hB⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHUpperCrossing
