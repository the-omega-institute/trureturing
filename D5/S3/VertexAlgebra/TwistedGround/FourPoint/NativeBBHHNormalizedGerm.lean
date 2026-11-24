/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBBHHNormalizedGerm
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native BBHH square-root-normalized continuation and cusp mode readout. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHUpperCrossing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Topology
open Bornology Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHNormalizedGerm

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd TwistedEven leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open NativeHBHBCanonicalContinuation (upperHalfPlane)
open NativeBHBHCanonicalContinuation
  (outerRoot outerRoot_eq innerRoot bhbhUpperAmplitude bhbhUpperAmplitude_analytic
    bhbhUpperAmplitude_hasSum_ab)
open NativeBBHHUpperCrossing
  (bbhh_b_hasSum_translated normalized_physical_roots bbhh_actual_upper_crossing_normalized)
open NativeMixedBProductUpperDisk (upperUnitDisk physicalOuterRoot physicalInnerRoot)
open NativeFixedCrossedProductToIterate
  (aJointTerm translationWeight shiftOuterMode fixed_a_joint_summable_of_homogeneous)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockCorrectedField (correctedField)
open Orbifold.NativeOddTwistedIntertwiner (OddCarrier)
open Orbifold.NativeOddUpperRightSkew
  (rightField rightField_coeff rightField_even_zero R_pairing_finite)
open Orbifold.NativeMixedPairField (mu)
open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private J_val odd_even_exponent_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open NativeFixedPairAIterate
  (fixedAExponent fixedAIterateCoeff fixedAIterateCoeff_eq_zero_off_energy)
open NativeMixedUpperProductCusp
  (bJointTerm bProductCoeff b_joint_product_hasSum bSewnNumerator)
open Orbifold.NativeFullMixedField (project)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain isOpen_slitDomain ball_subset_slitDomain)
open NativeMixedProductSlot23PhysicalRoots (b_joint_product_hasSum_scale)

open private physical_roots eval_translation_inverse from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHUpperCrossing
open private source_roots reversal_roots from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation
open private bEnergyTerm bEnergy_hasSum_iff bModeLinear bModeLinear_apply grade_mod_two
  opposite_grade_parities projected_basis_tensor BasisIndex basis from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private bEnergyTerm_factor bProductCoeff_summable_on_disk from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic
open private energySum energySum_analyticAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private sqrt_square zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private aModeLinear_apply fixed_a_off_diagonal from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private bSewnNumerator_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private mem_slitDomain from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open OriginalFourPointChartGluing (U_D U_D_eq)
open OriginalGaussianSewnAnalytic (coefficient)
open private entire_eq_reversed_taylor from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity
open private isPreconnected_U_D U_D_subset_puncturedPlane from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourPointChartGluing
open private slit_right_preconnected meromorphic_order_of_cusp from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBNormalizedGlobalMeromorphic

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

/-- The normalized BBHH value in the A convention. The inverse common root scale
acts in total doubled degree, and the opposite finite translation restores the
unshifted detector. -/
def bbhhNormalizedUpperAmplitude (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven) (y : ℂ) : ℂ :=
  Complex.sqrt y * ((outerRoot y * innerRoot y)⁻¹ ^ ((J : ℤ) - M - (6 + H + K)) *
    ∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(innerRoot y ^ (2 : ℕ))) j *
      bhbhUpperAmplitude M K P R Q ((L₁ false ^ j) S) y)

private theorem translated_bbhh_value (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperUnitDisk) :
    HasSum (bJointTerm true true R Q P S (outerRoot y * innerRoot y) (I * innerRoot y))
      (-(∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(innerRoot y ^ (2 : ℕ))) j *
        bhbhUpperAmplitude M K P R Q ((L₁ false ^ j) S) y)) := by
  let X := outerRoot y
  let Z := innerRoot y
  have h (j : ℕ) (hj : j ∈ Finset.range (J / 2 + 1)) :=
    bbhh_b_hasSum_translated M K H (J - 2 * j) P R Q ((L₁ false ^ j) S)
      hP hQ hR (lowered_grade hS (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) hy
  have hSum := hasSum_sum (s := Finset.range (J / 2 + 1)) fun j hj =>
    (h j hj).mul_left (translationWeight (-(Z ^ (2 : ℕ))) j)
  simp only [mul_neg, Finset.sum_neg_distrib, ← (physical_roots y).1, ← (physical_roots y).2]
    at hSum
  refine hSum.congr_fun fun i => ?_
  simp only [← bModeLinear_apply]
  exact (eval_translation_inverse (bModeLinear true true (X * Z) (I * Z) i R Q P)
    (Z ^ (2 : ℕ)) J S).symm

private theorem normalized_bbhh_b (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperUnitDisk) :
    HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
      (-bbhhNormalizedUpperAmplitude M K H J P R Q S y) := by
  let D := outerRoot y * innerRoot y
  let e : ℤ := (J : ℤ) - M - (6 + H + K)
  obtain ⟨hx, hz, _, _, _, _, _⟩ := reversal_roots hy.2
  obtain ⟨_, hinner, _⟩ := normalized_physical_roots hy
  have hc : D⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hx hz)
  have hOuter : D⁻¹ * D = 1 := inv_mul_cancel₀ (mul_ne_zero hx hz)
  have hInner : D⁻¹ * (I * innerRoot y) = Complex.sqrt y := by
    rw [mul_comm]
    exact hinner
  have hb := translated_bbhh_value M K H J P R Q S hP hQ hR hS hy
  change HasSum (bJointTerm true true R Q P S D (I * innerRoot y)) _ at hb
  by_cases hzero : R = 0 ∨ Q = 0
  · have hterm (x z : ℂ) (i : ℤ × ℤ) : bJointTerm true true R Q P S x z i = 0 := by
      rcases hzero with h | h <;> simp [← bModeLinear_apply, h]
    rw [bbhhNormalizedUpperAmplitude, ← mul_assoc, ← mul_neg]
    refine (hb.mul_left (Complex.sqrt y * D⁻¹ ^ e)).congr_fun fun i => ?_
    rw [hterm, hterm, mul_zero, mul_zero]
  · push Not at hzero
    have hHK := (opposite_grade_parities (s := true) R Q hR hQ hzero.1 hzero.2).1
    have hs := b_joint_product_hasSum_scale true true M H K J R Q P S
      hR hQ hP hS hHK hc hb
    rw [hOuter, hInner] at hs
    simpa only [bbhhNormalizedUpperAmplitude, D, e, mul_neg] using hs.mul_left (Complex.sqrt y)

private theorem analytic_normalized_bbhh (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven) :
    AnalyticOnNhd ℂ (bbhhNormalizedUpperAmplitude M K H J P R Q S) upperHalfPlane := by
  intro y hy
  obtain ⟨hX, hZ, _, _, _, haX, haZ⟩ := reversal_roots hy
  have ha := (source_roots hy).1
  exact ha.mul (((haX.mul haZ).inv (mul_ne_zero hX hZ) |>.zpow
      (inv_ne_zero (mul_ne_zero hX hZ))).mul
    (Finset.analyticAt_fun_sum _ fun j _ =>
      (((haZ.pow 2).neg.pow j).mul analyticAt_const).mul
        (bhbhUpperAmplitude_analytic M K P R Q ((L₁ false ^ j) S) y hy)))

private theorem bbhh_b_zero_series (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let k : ℤ := (5 + (H : ℤ) + K) / 2
    let a := bProductCoeff true true M H K J R Q P S
    AnalyticOnNhd ℂ (energySum a) (ball (0 : ℂ) 1) ∧
    (∀ y ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => a E * y ^ E) (energySum a y)) ∧
    (∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 →
      HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
        (y ^ (-k) * energySum a y)) := by
  intro k a
  by_cases hzero : R = 0 ∨ Q = 0 ∨ P = 0 ∨ S = 0
  · have hterm (x z : ℂ) (i : ℤ × ℤ) : bJointTerm true true R Q P S x z i = 0 := by
      rcases hzero with h | h | h | h <;> simp [← bModeLinear_apply, h]
    have ha (E : ℕ) : a E = 0 := by
      simpa only [a, bJointTerm, bProductCoeff, one_zpow, mul_one] using
        hterm 1 1 (2 * (E : ℤ) - (6 + (H : ℤ) + K), (J : ℤ) - M - 2 * (E : ℤ))
    have he : energySum a = fun _ => 0 := by funext y; simp [energySum, ha]
    simp only [he, ha, hterm, zero_mul, mul_zero]
    exact ⟨analyticOnNhd_const, fun _ _ => hasSum_zero, fun _ _ _ => hasSum_zero⟩
  push Not at hzero
  obtain ⟨hR₀, hQ₀, hP₀, hS₀⟩ := hzero
  obtain ⟨m, hm⟩ := (opposite_grade_parities (s := true) R Q hR hQ hR₀ hQ₀).1
  have hHK : Odd ((H : ℤ) + K) := ⟨m, hm⟩
  have hJM := (opposite_grade_parities (s := true) P S hP hS hP₀ hS₀).2
  have hs (w : ℂ) (hw : ‖w‖ < 1) : Summable (fun E : ℕ => a E * w ^ E) :=
    bProductCoeff_summable_on_disk true true M H K J R Q P S hR hQ hP hS hHK hJM hw
  refine ⟨fun y hy => energySum_analyticAt a hs (mem_ball_zero_iff.mp hy),
    fun y hy => (hs y (mem_ball_zero_iff.mp hy)).hasSum, ?_⟩
  intro y hy hy₀
  let ρ := Complex.sqrt y
  let pole : ℤ := 6 + (H : ℤ) + K
  have hρ : ρ ≠ 0 := fun h => hy₀ (by simpa [ρ, h] using (sqrt_square y).symm)
  have hscale : ρ * ρ ^ (-pole) = y ^ (-k) := by
    calc
      _ = ρ ^ (1 + -pole) := by rw [zpow_add₀ hρ, zpow_one]
      _ = _ := by
        rw [show 1 + -pole = 2 * (-k) by dsimp [pole, k]; omega, zpow_double, sqrt_square]
  have hEnergy : HasSum (bEnergyTerm true true M H K J R Q P S 1 ρ)
      (ρ ^ (-pole) * energySum a y) :=
    ((hs y (mem_ball_zero_iff.mp hy)).hasSum.mul_left (ρ ^ (-pole))).congr_fun
    (fun E => by
      rw [bEnergyTerm_factor true true M H K J R Q P S one_ne_zero hρ E]
      simp only [one_zpow, mul_one, div_one, ρ, sqrt_square, pole, a])
  have hb := (bEnergy_hasSum_iff true true M H K J R Q P S hR hQ hP hS hHK 1 ρ _).mp hEnergy
  simpa only [← mul_assoc, hscale] using hb.mul_left ρ

/-- The literal BBHH zero-cusp Laurent series and the upper continuation in
the A convention. The coefficient of exponent `E-k` is the negative native
B coefficient. The pole bound `k` depends only on the inner two sources. -/
theorem bbhh_actual_normalized_zero_germ (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let F := bbhhNormalizedUpperAmplitude M K H J P R Q S
    let k : ℤ := (5 + (H : ℤ) + K) / 2
    let a := bProductCoeff true true M H K J R Q P S
    let G (y : ℂ) := -energySum a y
    AnalyticOnNhd ℂ F upperHalfPlane ∧ AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) ∧
    (∀ y ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => -(a E) * y ^ E) (G y)) ∧
    (∀ y ∈ upperUnitDisk,
      F y = y ^ (-k) * G y ∧
      HasSum (fun E : ℕ => -(a E) * y ^ ((E : ℤ) - k)) (F y) ∧
      HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
        (-F y) ∧
      ((1 / 2 : ℝ) < y.re →
        HasSum (fun i => Complex.sqrt y *
          aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i) (F y))) := by
  intro F k a G
  obtain ⟨ha, hs, hb⟩ := bbhh_b_zero_series M K H J P R Q S hP hQ hR hS
  refine ⟨analytic_normalized_bbhh M K H J P R Q S, ha.neg, ?_, ?_⟩
  · intro y hy
    simpa only [neg_mul] using (hs y hy).neg
  · intro y hy
    have hB := normalized_bbhh_b M K H J P R Q S hP hQ hR hS hy
    have hy₀ : y ≠ 0 := fun h => by have hi := hy.2; simp [h] at hi
    have hval : F y = y ^ (-k) * G y := by
      have h := congrArg Neg.neg (hB.unique (hb y hy.1 hy₀))
      simpa only [neg_neg, ← mul_neg] using h
    refine ⟨hval, ?_, hB, ?_⟩
    · rw [hval]
      refine ((((hs y hy.1).neg).mul_left (y ^ (-k))).congr_fun fun E => ?_)
      rw [sub_eq_add_neg, zpow_add₀ hy₀, zpow_natCast]
      ring
    · intro hr
      obtain ⟨C, hA, hB'⟩ := bbhh_actual_upper_crossing_normalized P R Q S hy hr
      have h := congrArg Neg.neg (hB.unique (hB'.mul_left (Complex.sqrt y)))
      simp only [mul_neg, neg_neg] at h
      change F y = _ at h
      rw [h]
      exact hA.mul_left (Complex.sqrt y)

private def rightHalf : Set ℂ := {y | (1 / 2 : ℝ) < y.re}

private def collisionCoord (y : ℂ) : ℂ := (1 - y) / y

private theorem right_ne_zero {y : ℂ} (hy : y ∈ rightHalf) : y ≠ 0 := by
  rintro rfl
  norm_num [rightHalf] at hy

private theorem collisionCoord_mem_ball {y : ℂ} (hy : y ∈ rightHalf) :
    collisionCoord y ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, collisionCoord, norm_div, div_lt_one (norm_pos_iff.mpr (right_ne_zero hy))]
  exact (norm_one_sub_lt_iff y).mpr hy

set_option maxHeartbeats 1000000 in
private theorem a_energy_hasSum_iff (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    (hpar : Even ((M : ℤ) + H)) (d z value : ℂ) :
    HasSum (fun E : ℕ => fixedAIterateCoeff true M H K J (fixedAExponent M H E)
      P R Q.val S.val * (d ^ fixedAExponent M H E * z ^ ((J : ℤ) - K - 2 * (E : ℤ)))) value ↔
    HasSum (aJointTerm true false P R Q S d z) value := by
  let modes (E : ℕ) := (fixedAExponent M H E, (J : ℤ) - K - 2 * (E : ℤ))
  have hinj : Function.Injective modes := by
    intro E F h
    have hf := congrArg Prod.fst h
    dsimp [modes, fixedAExponent] at hf
    omega
  have hout (i : ℤ × ℤ) (hi : i ∉ Set.range modes) :
      aJointTerm true false P R Q S d z i = 0 := by
    obtain ⟨n, m⟩ := i
    by_cases hm : m = (J : ℤ) - K - (n + ((M : ℤ) + H + 6))
    · have hn : n ∉ Set.range (fixedAExponent M H) := by
        rintro ⟨E, hE⟩
        exact hi ⟨E, Prod.ext hE (by dsimp [modes]; rw [← hE] at hm; unfold fixedAExponent at hm; omega)⟩
      have hzero := fixedAIterateCoeff_eq_zero_off_energy true M H K J n P R Q.val S.val
        hP hR hpar hn
      rw [aJointTerm, hm]
      exact mul_eq_zero.mpr (Or.inl hzero)
    · rw [aJointTerm, fixed_a_off_diagonal true false M H K J P R Q S hP hR hQ hS hpar n m hm,
        zero_mul]
  have hterm (E : ℕ) :
      aJointTerm true false P R Q S d z (modes E) =
        fixedAIterateCoeff true M H K J (fixedAExponent M H E) P R Q.val S.val *
          (d ^ fixedAExponent M H E * z ^ ((J : ℤ) - K - 2 * (E : ℤ))) := by
    have he : (J : ℤ) - K - (fixedAExponent M H E + ((M : ℤ) + H + 6)) =
        (J : ℤ) - K - 2 * (E : ℤ) := by unfold fixedAExponent; ring
    simp only [aJointTerm, modes, fixedAIterateCoeff, he]
  have hEq : aJointTerm true false P R Q S d z ∘ modes = _ := funext hterm
  rw [← hEq]
  exact hinj.hasSum_iff hout

private theorem bbhh_a_collision_series (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let k : ℤ := ((M : ℤ) + H + 6) / 2
    let a (E : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H E) P R Q.val S.val
    AnalyticOnNhd ℂ (energySum a) (ball (0 : ℂ) 1) ∧
    (∀ w ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => a E * w ^ E) (energySum a w)) ∧
    (∀ y ∈ rightHalf, y ≠ 1 →
      HasSum (aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y))
        ((1 - y) ^ (-k) * (Complex.sqrt y ^ ((J : ℤ) - K) * energySum a (collisionCoord y)))) := by
  intro k a
  by_cases hzero : P = 0 ∨ R = 0
  · have hterm (d z : ℂ) (i : ℤ × ℤ) : aJointTerm true false P R Q S d z i = 0 := by
      rcases hzero with h | h <;> simp [← aModeLinear_apply, h]
    have ha (E : ℕ) : a E = 0 := by
      simpa only [a, fixedAIterateCoeff, aJointTerm, one_zpow, mul_one] using
        hterm 1 1 (fixedAExponent M H E, (J : ℤ) - K - (fixedAExponent M H E + ((M : ℤ) + H + 6)))
    have he : energySum a = fun _ => 0 := by funext y; simp [energySum, ha]
    simp only [he, ha, zero_mul, mul_zero]
    exact ⟨analyticOnNhd_const, fun _ _ => hasSum_zero, fun y _ _ =>
      hasSum_zero.congr_fun fun i => hterm _ _ i⟩
  push Not at hzero
  have hm := grade_mod_two (s := true) hP hzero.1
  have hh := grade_mod_two (s := true) hR hzero.2
  have hpar : Even ((M : ℤ) + H) := Int.even_iff.mpr (by simp at hm hh; omega)
  have hk : 2 * k = (M : ℤ) + H + 6 := by
    obtain ⟨m, hm⟩ := hpar
    dsimp [k]
    omega
  have hexp (E : ℕ) : fixedAExponent M H E = 2 * ((E : ℤ) - k) := by
    unfold fixedAExponent
    omega
  have hs (w : ℂ) (hw : ‖w‖ < 1) : Summable (fun E : ℕ => a E * w ^ E) := by
    by_cases hw₀ : w = 0
    · subst w
      apply summable_of_ne_finset_zero (s := {0})
      intro E hE
      have hne : E ≠ 0 := by simpa only [Finset.mem_singleton] using hE
      rw [zero_pow hne, mul_zero]
    let d := Complex.sqrt w
    have hd : d ≠ 0 := fun he => hw₀ (by simpa [d, he] using (sqrt_square w).symm)
    have hr : ‖d‖ < ‖(1 : ℂ)‖ := by
      rw [norm_one]
      apply (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp
      simpa only [← norm_pow, d, sqrt_square, one_pow] using hw
    have h := (fixed_a_joint_summable_of_homogeneous true false M H K J
      P R Q S hP hR hQ hS hd hr).hasSum
    have he := (a_energy_hasSum_iff M K H J P R Q S hP hQ hR hS hpar d 1 _).mpr h
    refine (he.mul_left (w ^ k)).summable.congr fun E => ?_
    have hpow : d ^ fixedAExponent M H E = w ^ ((E : ℤ) - k) := by
      rw [hexp, zpow_double, sqrt_square]
    simp only [hpow, a, one_zpow, mul_one]
    calc
      _ = (w ^ k * w ^ ((E : ℤ) - k)) * fixedAIterateCoeff true M H K J
          (fixedAExponent M H E) P R Q.val S.val := by ring
      _ = _ := by rw [← zpow_add₀ hw₀, show k + ((E : ℤ) - k) = E by ring, zpow_natCast, mul_comm]
  refine ⟨fun w hw => energySum_analyticAt a hs (mem_ball_zero_iff.mp hw),
    fun w hw => (hs w (mem_ball_zero_iff.mp hw)).hasSum, ?_⟩
  intro y hy h1
  let z := Complex.sqrt y
  let d := Complex.sqrt (1 - y)
  have hz₀ := right_ne_zero hy
  have hd₀ := sub_ne_zero.mpr (Ne.symm h1)
  have hz : z ≠ 0 := fun he => hz₀ (by simpa [z, he] using (sqrt_square y).symm)
  apply (a_energy_hasSum_iff M K H J P R Q S hP hQ hR hS hpar d z _).mp
  let c := (1 - y) ^ (-k) * z ^ ((J : ℤ) - K)
  have hev := ((hs _ (mem_ball_zero_iff.mp (collisionCoord_mem_ball hy))).hasSum.mul_left c)
  refine (show HasSum _ ((1 - y) ^ (-k) * (z ^ ((J : ℤ) - K) * energySum a (collisionCoord y))) from
    by simpa only [c, mul_assoc, energySum] using hev).congr_fun fun E => ?_
  have dPow : d ^ fixedAExponent M H E = (1 - y) ^ (-k) * (1 - y) ^ E := by
    rw [hexp, zpow_double, sqrt_square, show (E : ℤ) - k = -k + E by ring,
      zpow_add₀ hd₀, zpow_natCast]
  have zPow : z ^ ((J : ℤ) - K - 2 * (E : ℤ)) = z ^ ((J : ℤ) - K) * (y ^ E)⁻¹ := by
    rw [sub_eq_add_neg, zpow_add₀ hz, zpow_neg, zpow_double, sqrt_square, zpow_natCast]
  rw [dPow, zPow, collisionCoord, div_pow, div_eq_mul_inv]
  dsimp only [a, c]
  ring

/-- In the collision coordinate `(1-y)/y`, the native BBHH iterate has a
convergent series of its fixed-pair coefficients. After restoring the
analytic unit and the pole at one, it gives the same normalized upper
amplitude as the B germ. -/
theorem bbhh_actual_normalized_collision_germ (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let F := bbhhNormalizedUpperAmplitude M K H J P R Q S
    let k : ℤ := ((M : ℤ) + H + 6) / 2
    let a (E : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H E) P R Q.val S.val
    let G (y : ℂ) := Complex.sqrt y * (Complex.sqrt y ^ ((J : ℤ) - K) *
      energySum a ((1 - y) / y))
    AnalyticOnNhd ℂ G {y : ℂ | (1 / 2 : ℝ) < y.re} ∧
    (∀ w ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => a E * w ^ E) (energySum a w)) ∧
    (∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
      HasSum (fun i => Complex.sqrt y *
        aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i)
        ((1 - y) ^ (-k) * G y)) ∧
    (∀ y : ℂ, 0 < y.im → (1 / 2 : ℝ) < y.re → F y = (1 - y) ^ (-k) * G y) := by
  intro F k a G
  obtain ⟨ha, hs, hA⟩ := bbhh_a_collision_series M K H J P R Q S hP hQ hR hS
  have hG : AnalyticOnNhd ℂ G rightHalf := by
    intro y hy
    have hr : (1 / 2 : ℝ) < y.re := hy
    have hz := right_ne_zero hy
    have hsqrt : AnalyticAt ℂ Complex.sqrt y :=
      Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y
        (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)))
    have hroot : Complex.sqrt y ≠ 0 := fun he => hz (by simpa [he] using (sqrt_square y).symm)
    have hratio : AnalyticAt ℂ collisionCoord y := (analyticAt_const.sub analyticAt_id).div
      analyticAt_id hz
    exact hsqrt.mul ((hsqrt.zpow hroot).mul ((ha (collisionCoord y) (collisionCoord_mem_ball hy)).comp hratio))
  have hSum (y : ℂ) (hy : y ∈ rightHalf) (h1 : y ≠ 1) :
      HasSum (fun i => Complex.sqrt y *
        aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i)
        ((1 - y) ^ (-k) * G y) := by
    convert (hA y hy h1).mul_left (Complex.sqrt y) using 1
    dsimp only [G, collisionCoord]
    ring
  refine ⟨hG, hs, hSum, ?_⟩
  let U := upperHalfPlane ∩ rightHalf
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt continuous_const Complex.continuous_re)
  have hConn : IsPreconnected U :=
    ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_re_gt (1 / 2 : ℝ))).isPreconnected
  have hOne (y : ℂ) (hy : y ∈ upperHalfPlane) : y ≠ 1 := by
    rintro rfl
    norm_num [upperHalfPlane] at hy
  have hComp : AnalyticOnNhd ℂ (fun y => (1 - y) ^ (-k) * G y) U := by
    intro y hy
    exact (((analyticAt_const (v := (1 : ℂ))).sub analyticAt_id).zpow
      (sub_ne_zero.mpr (hOne y hy.1).symm)).mul (hG y hy.2)
  let y₀ : ℂ := ⟨3 / 4, 1 / 4⟩
  have hy₀ : y₀ ∈ U := by norm_num [U, upperHalfPlane, rightHalf, y₀]
  have hyb : y₀ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    apply (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply, y₀]
  have hPatch : F =ᶠ[𝓝 y₀] fun y => (1 - y) ^ (-k) * G y := by
    filter_upwards [hU.eventually_mem hy₀, isOpen_ball.eventually_mem hyb] with y hy hb
    have hLens := (bbhh_actual_normalized_zero_germ M K H J P R Q S hP hQ hR hS).2.2.2 y ⟨hb, hy.1⟩
    exact (hLens.2.2.2 hy.2).unique (hSum y hy.2 (hOne y hy.1))
  have hF : AnalyticOnNhd ℂ F U := (analytic_normalized_bbhh M K H J P R Q S).mono inter_subset_left
  have he := hF.eqOn_of_preconnected_of_eventuallyEq hComp hConn hy₀ hPatch
  exact fun y hi hr => he (show y ∈ U from ⟨hi, hr⟩)

set_option maxHeartbeats 3500000 in
private theorem bbhh_b_slit_numerator (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let k : ℤ := (5 + (H : ℤ) + K) / 2
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G slitDomain ∧
      ∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 →
        HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
          (y ^ (-k) * G y) := by
  classical
  intro k
  by_cases hz : R = 0 ∨ Q = 0 ∨ P = 0 ∨ S = 0
  · refine ⟨fun _ => 0, analyticOnNhd_const, fun y _ _ => ?_⟩
    rw [mul_zero]
    refine hasSum_zero.congr_fun fun i => ?_
    rcases hz with h | h | h | h <;> simp [← bModeLinear_apply, h]
  push Not at hz
  obtain ⟨hR₀, hQ₀, hP₀, hS₀⟩ := hz
  have hHK := (opposite_grade_parities (s := true) R Q hR hQ hR₀ hQ₀).1
  have hJM := (opposite_grade_parities (s := true) P S hP hS hP₀ hS₀).2
  let cR := basis.repr R.val
  let cQ := basis.repr Q.val
  let cP := basis.repr P.val
  let cS := basis.repr S.val
  let R' (r : BasisIndex) := project true (basis r)
  let Q' (q : BasisIndex) := project false (basis q)
  let P' (p : BasisIndex) := project true (basis p)
  let S' (s : BasisIndex) := project false (basis s)
  have hBasis (r q p s : BasisIndex) :
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g slitDomain ∧
        (r ∈ cR.support → q ∈ cQ.support → p ∈ cP.support → s ∈ cS.support →
          ∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 →
            HasSum (fun i => Complex.sqrt y *
              bJointTerm true true (R' r) (Q' q) (P' p) (S' s) 1 (Complex.sqrt y) i)
              (y ^ (-k) * g y)) := by
    by_cases h : r ∈ cR.support ∧ q ∈ cQ.support ∧ p ∈ cP.support ∧ s ∈ cS.support
    · obtain ⟨hr, hq, hp, hs⟩ := h
      obtain ⟨hrG, Vr, ur, hrT⟩ := projected_basis_tensor true H R hR r hr
      obtain ⟨hqG, Vq, uq, hqT⟩ := projected_basis_tensor false K Q hQ q hq
      obtain ⟨hpG, Vp, up, hpT⟩ := projected_basis_tensor true M P hP p hp
      obtain ⟨hsG, Vs, us, hsT⟩ := projected_basis_tensor false J S hS s hs
      let phase := I ^ ((K : ℤ) + J - M - 2 * (H : ℤ) - 3)
      let num := bSewnNumerator H K J Vp Vr Vq Vs up ur uq us
      refine ⟨fun y => phase * num y, fun y hy => analyticAt_const.mul ?_, ?_⟩
      · have hdiff : DifferentiableOn ℂ num slitDomain :=
          bSewnNumerator_differentiableOn H K J Vp Vr Vq Vs up ur uq us
        exact hdiff.analyticOnNhd isOpen_slitDomain y hy
      · intro _ _ _ _ y hy hy₀
        let ρ := Complex.sqrt y
        have hρ : ρ ≠ 0 := fun he => hy₀ (by simpa [ρ, he] using (sqrt_square y).symm)
        have hrad : ‖ρ‖ < 1 := by
          apply (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp
          simpa only [← norm_pow, ρ, sqrt_square, one_pow] using mem_ball_zero_iff.mp hy
        have hsum := b_joint_product_hasSum true true M H K J
          (R' r) (Q' q) (P' p) (S' s) Vp Vr Vq Vs up ur uq us
          hrG hqG hpG hsG hrT hqT hpT hsT hHK hJM (xRoot := 1) (zRoot := ρ) one_ne_zero
          (by simpa only [div_one] using norm_pos_iff.mpr hρ) (by simpa only [div_one] using hrad)
        have hpow : ρ * ρ ^ (-(6 + (H : ℤ) + K)) = y ^ (-k) := by
          obtain ⟨m, hm⟩ := hHK
          calc
            _ = ρ ^ (1 + -(6 + (H : ℤ) + K)) := by rw [zpow_add₀ hρ, zpow_one]
            _ = _ := by
              rw [show 1 + -(6 + (H : ℤ) + K) = 2 * (-k) by dsimp [k]; omega,
                zpow_double, sqrt_square]
        have h := hsum.mul_left ρ
        simp only [one_zpow, one_mul, div_one] at h
        rw [show ρ ^ (2 : ℕ) = y from sqrt_square y] at h
        change HasSum _ (ρ * (ρ ^ (-(6 + (H : ℤ) + K)) * phase * num y)) at h
        rw [← mul_assoc, ← mul_assoc, hpow, mul_assoc] at h
        exact h
    · exact ⟨fun _ => 0, analyticOnNhd_const, fun hr hq hp hs => (h ⟨hr, hq, hp, hs⟩).elim⟩
  choose g hg using hBasis
  let G (y : ℂ) := ∑ r ∈ cR.support, cR r * (∑ q ∈ cQ.support, cQ q *
    (∑ p ∈ cP.support, cP p * (∑ s ∈ cS.support, cS s * g r q p s y)))
  have hdistrib (v : ℂ) (f : BasisIndex → BasisIndex → BasisIndex → BasisIndex → ℂ) :
      v * (∑ r ∈ cR.support, cR r * (∑ q ∈ cQ.support, cQ q *
        (∑ p ∈ cP.support, cP p * (∑ s ∈ cS.support, cS s * f r q p s)))) =
      ∑ r ∈ cR.support, cR r * (∑ q ∈ cQ.support, cQ q *
        (∑ p ∈ cP.support, cP p * (∑ s ∈ cS.support, cS s * (v * f r q p s)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_left_comm v (cR r), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_left_comm v (cQ q), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_left_comm v (cP p), Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => mul_left_comm v (cS s) (f r q p s)
  refine ⟨G, ?_, ?_⟩
  · intro y hy
    exact Finset.analyticAt_fun_sum _ fun r _ => analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun q _ => analyticAt_const.mul
        (Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul
          (Finset.analyticAt_fun_sum _ fun s _ => analyticAt_const.mul ((hg r q p s).1 y hy))))
  · intro y hy hy₀
    let ρ := Complex.sqrt y
    let f := bModeLinear true true 1 ρ
    have hexpand (i : ℤ × ℤ) :
        bJointTerm true true R Q P S 1 ρ i =
          ∑ r ∈ cR.support, cR r * (∑ q ∈ cQ.support, cQ q *
            (∑ p ∈ cP.support, cP p * (∑ s ∈ cS.support, cS s *
              f i (R' r) (Q' q) (P' p) (S' s)))) := by
      rw [← bModeLinear_apply]
      conv_lhs =>
        rw [← sum_projectedBasis true R]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [← sum_projectedBasis false Q]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [← sum_projectedBasis true P]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [← sum_projectedBasis false S]
        simp only [map_sum, map_smul, smul_eq_mul]
    have he := hasSum_sum (s := cR.support) fun r hr => HasSum.mul_left (cR r) <|
      hasSum_sum (s := cQ.support) fun q hq => HasSum.mul_left (cQ q) <|
      hasSum_sum (s := cP.support) fun p hp => HasSum.mul_left (cP p) <|
      hasSum_sum (s := cS.support) fun s hs =>
        ((hg r q p s).2 hr hq hp hs y hy hy₀).mul_left (cS s)
    rw [show y ^ (-k) * G y = _ from hdistrib _ (fun r q p s => g r q p s y)]
    refine he.congr_fun fun i => ?_
    change ρ * bJointTerm true true R Q P S 1 ρ i = _
    rw [hexpand i, hdistrib]
    simp only [f, bModeLinear_apply, ρ]

set_option maxHeartbeats 1600000 in
/-- The square-root-normalized BBHH B product and fixed A iterate are two
literal charts of one meromorphic function on the finite plane. Both halves
of each chart use the indicated principal roots. The only possible finite
poles are at zero and one, and the exact orders are determined by the native
energy series. -/
theorem bbhh_actual_normalized_finite_plane (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let F := bbhhNormalizedUpperAmplitude M K H J P R Q S
    let k₀ : ℤ := (5 + (H : ℤ) + K) / 2
    let k₁ : ℤ := ((M : ℤ) + H + 6) / 2
    let B₀ (y : ℂ) := -energySum (bProductCoeff true true M H K J R Q P S) y
    let A₁ (E : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H E) P R Q.val S.val
    let G₁ (y : ℂ) := Complex.sqrt y * (Complex.sqrt y ^ ((J : ℤ) - K) *
      energySum A₁ ((1 - y) / y))
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L ({0, 1} : Set ℂ)ᶜ ∧ Meromorphic L ∧
      (∀ y ∈ upperHalfPlane, L y = F y) ∧
      (∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 →
        HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
          (-L y) ∧ L y = y ^ (-k₀) * B₀ y) ∧
      (∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
        HasSum (fun i => Complex.sqrt y *
          aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i) (L y) ∧
          L y = (1 - y) ^ (-k₁) * G₁ y) ∧
      meromorphicOrderAt L 0 = ((-k₀ : ℤ) : WithTop ℤ) + meromorphicOrderAt B₀ 0 ∧
      meromorphicOrderAt L 1 = ((-k₁ : ℤ) : WithTop ℤ) + meromorphicOrderAt G₁ 1 := by
  classical
  intro F k₀ k₁ B₀ A₁ G₁
  obtain ⟨G₀, hG₀, hBSlit⟩ := bbhh_b_slit_numerator M K H J P R Q S hP hQ hR hS
  obtain ⟨hG₁, _, hA, hAUpper⟩ := bbhh_actual_normalized_collision_germ M K H J P R Q S hP hQ hR hS
  obtain ⟨hB₀, _, hBDisk⟩ := bbhh_b_zero_series M K H J P R Q S hP hQ hR hS
  let U₀ := slitDomain \ ({0} : Set ℂ)
  let U₁ := rightHalf \ ({1} : Set ℂ)
  let L₀ (y : ℂ) := -(y ^ (-k₀) * G₀ y)
  let L₁' (y : ℂ) := (1 - y) ^ (-k₁) * G₁ y
  have hOpenR : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hOpen₀ : IsOpen U₀ := isOpen_slitDomain.sdiff isClosed_singleton
  have hOpen₁ : IsOpen U₁ := hOpenR.sdiff isClosed_singleton
  have hOpenUpper : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  have hSlit₁ {y : ℂ} (hy : y ∈ slitDomain) : y ≠ 1 := by
    rintro rfl
    simpa using (mem_slitDomain _).mp hy
  have hUpper₀ {y : ℂ} (hy : y ∈ upperHalfPlane) : y ∈ U₀ := by
    change 0 < y.im at hy
    refine ⟨(mem_slitDomain _).mpr (Or.inr hy.ne'), ?_⟩
    rintro rfl
    simp at hy
  have hInter : U₀ ∩ U₁ = slitDomain ∩ rightHalf := by
    ext y
    exact ⟨fun ⟨hs, hr⟩ => ⟨hs.1, hr.1⟩,
      fun ⟨hs, hr⟩ => ⟨⟨hs, right_ne_zero hr⟩, ⟨hr, hSlit₁ hs⟩⟩⟩
  have hCover : U₀ ∪ U₁ = ({0, 1} : Set ℂ)ᶜ := by
    ext y
    change (y ∈ slitDomain ∧ y ≠ 0) ∨ (y ∈ rightHalf ∧ y ≠ 1) ↔ _
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨fun h => h.elim (fun ⟨hs, h₀⟩ => ⟨h₀, hSlit₁ hs⟩)
      (fun ⟨hr, h₁⟩ => ⟨right_ne_zero hr, h₁⟩), ?_⟩
    intro ⟨h₀, h₁⟩
    by_cases hs : y ∈ slitDomain
    · exact Or.inl ⟨hs, h₀⟩
    · have hre : 1 ≤ y.re := le_of_not_gt fun h => hs ((mem_slitDomain _).mpr (Or.inl h))
      exact Or.inr ⟨lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 1) hre, h₁⟩
  have hAn₀ : AnalyticOnNhd ℂ L₀ U₀ :=
    fun y hy => ((analyticAt_id.zpow hy.2).mul (hG₀ y hy.1)).neg
  have hAn₁ : AnalyticOnNhd ℂ L₁' U₁ := by
    intro y hy
    have hb : AnalyticAt ℂ (fun z : ℂ => 1 - z) y := analyticAt_const.sub analyticAt_id
    exact (hb.zpow (sub_ne_zero.mpr (Ne.symm hy.2))).mul (hG₁ y hy.1)
  have hF : AnalyticOnNhd ℂ F upperHalfPlane := analytic_normalized_bbhh M K H J P R Q S
  have h₀upper : EqOn L₀ F upperHalfPlane := by
    let y₀ : ℂ := (1 / 2 : ℂ) * I
    have hY : y₀ ∈ upperHalfPlane := by norm_num [y₀, upperHalfPlane, Complex.mul_im]
    have hY' : y₀ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      norm_num [y₀, norm_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    refine (hAn₀.mono (fun _ hy => hUpper₀ hy)).eqOn_of_preconnected_of_eventuallyEq hF
      (convex_halfSpace_im_gt 0).isPreconnected hY ?_
    filter_upwards [hOpenUpper.eventually_mem hY, isOpen_ball.eventually_mem hY'] with y hu hb
    have h := (hBSlit y hb (hUpper₀ hu).2).unique
      (normalized_bbhh_b M K H J P R Q S hP hQ hR hS ⟨hb, hu⟩)
    simpa only [L₀, neg_neg] using congrArg Neg.neg h
  have hOverlap : EqOn L₀ L₁' (U₀ ∩ U₁) := by
    let y₀ : ℂ := ⟨3 / 4, 1 / 4⟩
    have hyu : y₀ ∈ upperHalfPlane := by norm_num [y₀, upperHalfPlane]
    have hyr : y₀ ∈ rightHalf := by norm_num [y₀, rightHalf]
    refine (hAn₀.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (hAn₁.mono inter_subset_right) ?_ ⟨hUpper₀ hyu, hyr, hSlit₁ (hUpper₀ hyu).1⟩ ?_
    · rw [hInter]
      exact slit_right_preconnected
    · filter_upwards [hOpenUpper.eventually_mem hyu, hOpenR.eventually_mem hyr] with y hy hr
      exact (h₀upper hy).trans (hAUpper y hy hr)
  let L := U₀.piecewise L₀ L₁'
  have hL₀ : EqOn L L₀ U₀ := fun _ hy => piecewise_eq_of_mem _ _ _ hy
  have hL₁ : EqOn L L₁' U₁ := by
    intro y hy
    by_cases hy₀ : y ∈ U₀
    · exact (hL₀ hy₀).trans (hOverlap ⟨hy₀, hy⟩)
    · exact piecewise_eq_of_notMem _ _ _ hy₀
  have hHol : AnalyticOnNhd ℂ L ({0, 1} : Set ℂ)ᶜ := by
    rw [← hCover]
    rintro y (hy | hy)
    · exact (hAn₀ y hy).congr ((hOpen₀.eventually_mem hy).mono fun _ hz => (hL₀ hz).symm)
    · exact (hAn₁ y hy).congr ((hOpen₁.eventually_mem hy).mono fun _ hz => (hL₁ hz).symm)
  have hLocal₀ (y : ℂ) (hy : y ∈ ball (0 : ℂ) 1) (hy₀ : y ≠ 0) : L y = y ^ (-k₀) * B₀ y := by
    have h := congrArg Neg.neg ((hBSlit y hy hy₀).unique (hBDisk y hy hy₀))
    simpa only [L₀, B₀, ← mul_neg] using (hL₀ ⟨ball_subset_slitDomain hy, hy₀⟩).trans h
  have hNear₀ : L =ᶠ[𝓝[≠] (0 : ℂ)] fun y => y ^ (-k₀) * B₀ y := by
    have hBall : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ ball 0 1 := ball_mem_nhds 0 zero_lt_one
    filter_upwards [hBall.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hy hn
    exact hLocal₀ y hy hn
  have hNear₁ : L =ᶠ[𝓝[≠] (1 : ℂ)] L₁' := by
    have hOne : (1 : ℂ) ∈ rightHalf := by norm_num [rightHalf]
    filter_upwards [(hOpenR.eventually_mem hOne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hy hn
    exact hL₁ ⟨hy, hn⟩
  have hOrd₀ := meromorphic_order_of_cusp (-k₀) (t := fun z => z) analyticAt_id rfl
    (by simp) ((hB₀ 0 (mem_ball_self zero_lt_one)).neg) hNear₀
  have hOrd₁ := meromorphic_order_of_cusp (-k₁) (t := fun y : ℂ => 1 - y)
    (analyticAt_const.sub analyticAt_id) (by simp) (by simp)
    (hG₁ 1 (by norm_num)) hNear₁
  refine ⟨L, hHol, ?_, fun y hy => (hL₀ (hUpper₀ hy)).trans (h₀upper hy), ?_, ?_, hOrd₀.2, hOrd₁.2⟩
  · intro y
    by_cases hy₀ : y = 0
    · exact hy₀ ▸ hOrd₀.1
    by_cases hy₁ : y = 1
    · exact hy₁ ▸ hOrd₁.1
    exact (hHol y (by simp [hy₀, hy₁])).meromorphicAt
  · intro y hy hy₀
    refine ⟨?_, hLocal₀ y hy hy₀⟩
    rw [hL₀ ⟨ball_subset_slitDomain hy, hy₀⟩]
    simpa only [L₀, neg_neg] using hBSlit y hy hy₀
  · intro y hy hy₁
    exact ⟨(hL₁ (show y ∈ U₁ from ⟨hy, hy₁⟩)).symm ▸ hA y hy hy₁, hL₁ ⟨hy, hy₁⟩⟩

set_option maxHeartbeats 1200000 in
private theorem reversed_b_modes (J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven)
    (hS : S.val ∈ actualGrade ℒ leechUnit J) {d z : ℂ} (hz : z ≠ 0) (i : ℤ × ℤ) :
    bJointTerm true true P Q R S (I * z) d i =
      -(∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(z ^ (2 : ℕ))) j *
        NativeMixedAIterateRadial.aJointTerm true P Q R.val ((L₁ false ^ j) S).val
          d z (shiftOuterMode j i)) := by
  obtain ⟨m, e⟩ := i
  let a : OddCarrier ℒ := (mu true P).coeff m Q
  change actualForm ℒ leechUnit S.val ((rightField ℒ leechUnit true R).coeff e a).val *
      (d ^ m * (I * z) ^ e) =
    -(∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(z ^ (2 : ℕ))) j *
      (actualForm ℒ leechUnit ((L₁ false ^ j) S).val
        ((correctedField ℒ leechUnit a.val).coeff (e - 2 * (j : ℤ)) R.val) *
        (d ^ m * z ^ (e - 2 * (j : ℤ)))))
  by_cases he : Even e
  · rw [rightField_even_zero ℒ leechUnit true e he, Submodule.coe_zero, map_zero, zero_mul]
    rw [← Finset.sum_neg_distrib]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    have he' : Even (e - 2 * (j : ℤ)) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - (j : ℤ), by omega⟩
    rw [odd_even_exponent_zero ℒ leechUnit a _ he', map_zero, zero_mul, mul_zero, neg_zero]
  · have hOdd := Int.not_even_iff_odd.mp he
    obtain ⟨k, hk⟩ := hOdd
    let n : ℤ := -k - 2
    have hn : -2 * n - 3 = e := by dsimp [n]; omega
    rw [← hn, rightField_coeff ℒ leechUnit true n R a, R_pairing_finite ℒ leechUnit true n J R a S hS,
      Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hmode : -2 * (n + (j : ℤ)) - 3 = e - 2 * (j : ℤ) := by omega
    simp only [J_val, hmode, hn, lowering_pow_val, translationWeight]
    have hphase : I ^ (e - 2 * (j : ℤ)) * I ^ e = -((-1 : ℂ) ^ j) := by
      have he' : Odd e := ⟨k, hk⟩
      rw [← zpow_add₀ Complex.I_ne_zero, show e - 2 * (j : ℤ) + e =
          2 * e + 2 * (-(j : ℤ)) by ring, zpow_add₀ Complex.I_ne_zero,
        zpow_double, zpow_double, Complex.I_sq, he'.neg_one_zpow, zpow_neg, zpow_natCast,
        ← inv_pow, inv_neg, inv_one, neg_one_mul]
    have hpower : z ^ e = (z ^ (2 : ℕ)) ^ j * z ^ (e - 2 * (j : ℤ)) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ hz]
      congr 1
      push_cast
      ring
    rw [mul_zpow, hpower, neg_eq_neg_one_mul (z ^ (2 : ℕ)), mul_pow]
    calc
      _ = (I ^ (e - 2 * (j : ℤ)) * I ^ e) *
          ((j.factorial : ℂ)⁻¹ *
            (actualForm ℒ leechUnit ((L₁ false ^ j) S).val
              ((correctedField ℒ leechUnit a.val).coeff (e - 2 * (j : ℤ)) R.val) *
              (d ^ m * ((z ^ (2 : ℕ)) ^ j * z ^ (e - 2 * (j : ℤ)))))) := by simp only [lowering_pow_val]; ring
      _ = _ := by rw [hphase]; simp only [lowering_pow_val]; ring

private theorem normalized_bbhh_reversed_b (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperHalfPlane) (he : 1 < ‖y‖) :
    HasSum (fun i => Complex.sqrt y * bJointTerm true true P Q R S (Complex.sqrt y) 1 i)
      (-bbhhNormalizedUpperAmplitude M K H J P R Q S y) := by
  let X := outerRoot y
  let Z := innerRoot y
  let D := X * Z
  let e : ℤ := (J : ℤ) - M - (6 + H + K)
  have h (j : ℕ) (hj : j ∈ Finset.range (J / 2 + 1)) :=
    (bhbhUpperAmplitude_hasSum_ab M K H (J - 2 * j) P R Q ((L₁ false ^ j) S)
      hP hQ hR (lowered_grade hS (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) hy).1 he
  obtain ⟨hx, hz, _, _, _, _, _⟩ := reversal_roots hy
  have hb : HasSum (bJointTerm true true P Q R S (I * Z) D)
      (-(∑ j ∈ Finset.range (J / 2 + 1), translationWeight (-(Z ^ (2 : ℕ))) j *
        bhbhUpperAmplitude M K P R Q ((L₁ false ^ j) S) y)) := by
    refine (hasSum_sum (s := Finset.range (J / 2 + 1)) fun j hj =>
      ((shiftOuterMode j).hasSum_iff.mpr (h j hj)).mul_left
        (translationWeight (-(Z ^ (2 : ℕ))) j)).neg.congr_fun ?_
    intro i
    exact reversed_b_modes J P R Q S hS hz i
  have hc : D⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hx hz)
  have hInner : D⁻¹ * D = 1 := inv_mul_cancel₀ (mul_ne_zero hx hz)
  have hOuter : D⁻¹ * (I * Z) = Complex.sqrt y := by
    have hr := (source_roots hy).2.2.1
    dsimp only [D, X]
    rw [outerRoot_eq]
    field_simp [hz, hr, Complex.I_ne_zero]
    exact div_self (show Z ≠ 0 from hz)
  by_cases hzero : P = 0 ∨ Q = 0
  · have hterm (x z : ℂ) (i : ℤ × ℤ) : bJointTerm true true P Q R S x z i = 0 := by
      rcases hzero with h | h <;> simp [← bModeLinear_apply, h]
    rw [bbhhNormalizedUpperAmplitude, ← mul_assoc, ← mul_neg]
    refine (hb.mul_left (Complex.sqrt y * D⁻¹ ^ e)).congr_fun fun i => ?_
    rw [hterm, hterm, mul_zero, mul_zero]
  · push Not at hzero
    have hMK := (opposite_grade_parities (s := true) P Q hP hQ hzero.1 hzero.2).1
    have hs := b_joint_product_hasSum_scale true true H M K J P Q R S hP hQ hR hS hMK hc hb
    rw [hInner, hOuter] at hs
    rw [show (J : ℤ) - H - (6 + (M : ℤ) + K) = (J : ℤ) - M - (6 + (H : ℤ) + K) by ring] at hs
    simpa only [bbhhNormalizedUpperAmplitude, D, X, Z, mul_neg] using
      hs.mul_left (Complex.sqrt y)

private theorem bbhh_b_infinity_series (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let k : ℤ := (1 + (J : ℤ) - H) / 2
    let a := bProductCoeff true true H M K J P Q R S
    ∀ y : ℂ, 1 < ‖y‖ →
      HasSum (fun i => Complex.sqrt y * bJointTerm true true P Q R S (Complex.sqrt y) 1 i)
        (y ^ k * energySum a y⁻¹) := by
  intro k a y hy
  by_cases hzero : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0
  · have hterm (x z : ℂ) (i : ℤ × ℤ) : bJointTerm true true P Q R S x z i = 0 := by
      rcases hzero with h | h | h | h <;> simp [← bModeLinear_apply, h]
    have ha (E : ℕ) : a E = 0 := by
      simpa only [a, bJointTerm, bProductCoeff, one_zpow, mul_one] using
        hterm 1 1 (2 * (E : ℤ) - (6 + (M : ℤ) + K), (J : ℤ) - H - 2 * (E : ℤ))
    simp only [energySum, ha, hterm, zero_mul, tsum_zero, mul_zero]
    exact hasSum_zero
  push Not at hzero
  obtain ⟨hP₀, hQ₀, hR₀, hS₀⟩ := hzero
  have hMK := (opposite_grade_parities (s := true) P Q hP hQ hP₀ hQ₀).1
  have hJH := (opposite_grade_parities (s := true) R S hR hS hR₀ hS₀).2
  have hy₀ := norm_pos_iff.mp (zero_lt_one.trans hy)
  let ρ := Complex.sqrt y
  have hρ : ρ ≠ 0 := fun h => hy₀ (by simpa [ρ, h] using (sqrt_square y).symm)
  have hyInv : y⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hy
  have hs := (bbhh_b_zero_series H K M J R P Q S hR hQ hP hS).2.1 y⁻¹ hyInv
  have hEnergy : HasSum (bEnergyTerm true true H M K J P Q R S ρ 1)
      (ρ ^ ((J : ℤ) - H) * energySum a y⁻¹) := by
    refine (hs.mul_left (ρ ^ ((J : ℤ) - H))).congr_fun fun E => ?_
    rw [bEnergyTerm_factor true true H M K J P Q R S hρ one_ne_zero E,
      one_zpow, one_mul, one_div, inv_pow, sqrt_square]
  have hb := (bEnergy_hasSum_iff true true H M K J P Q R S hP hQ hR hS hMK ρ 1 _).mp hEnergy
  have hpow : ρ * ρ ^ ((J : ℤ) - H) = y ^ k := by
    obtain ⟨m, hm⟩ := hJH
    calc
      _ = ρ ^ (1 + ((J : ℤ) - H)) := by rw [zpow_add₀ hρ, zpow_one]
      _ = _ := by
        rw [show 1 + ((J : ℤ) - H) = 2 * k by dsimp [k]; omega, zpow_double, sqrt_square]
  simpa only [← mul_assoc, hpow] using hb.mul_left ρ

set_option maxHeartbeats 2000000 in
/-- All three literal BBHH channels are obtained from one meromorphic
function on the sphere. The right-skew B products have sign minus in the
A convention, at both zero and infinity. The cusp exponents at zero and
one depend on the sources only. Infinity reads the reversed B modes. -/
theorem bbhh_actual_normalized_global_meromorphic (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let F := bbhhNormalizedUpperAmplitude M K H J P R Q S
    let k₀ : ℤ := (5 + (H : ℤ) + K) / 2
    let k₁ : ℤ := ((M : ℤ) + H + 6) / 2
    let kInf : ℤ := (1 + (J : ℤ) - H) / 2
    let B₀ (y : ℂ) := -energySum (bProductCoeff true true M H K J R Q P S) y
    let A₁ (E : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H E) P R Q.val S.val
    let G₁ (y : ℂ) := Complex.sqrt y * (Complex.sqrt y ^ ((J : ℤ) - K) *
      energySum A₁ ((1 - y) / y))
    let aInf := bProductCoeff true true H M K J P Q R S
    let BInf (z : ℂ) := -energySum aInf z
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L ({0, 1} : Set ℂ)ᶜ ∧ Meromorphic L ∧
      MeromorphicAt (fun z => L z⁻¹) 0 ∧
      (∀ y ∈ upperHalfPlane, L y = F y) ∧
      (∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 →
        HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
          (-L y) ∧ L y = y ^ (-k₀) * B₀ y) ∧
      (∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
        HasSum (fun i => Complex.sqrt y *
          aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i) (L y) ∧
          L y = (1 - y) ^ (-k₁) * G₁ y) ∧
      (∀ y : ℂ, 1 < ‖y‖ →
        HasSum (fun i => Complex.sqrt y * bJointTerm true true P Q R S (Complex.sqrt y) 1 i)
          (-L y) ∧ L y = y ^ kInf * BInf y⁻¹) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasSum (fun E : ℕ => -(aInf E) * z ^ E) (BInf z)) ∧
      meromorphicOrderAt L 0 = ((-k₀ : ℤ) : WithTop ℤ) + meromorphicOrderAt B₀ 0 ∧
      meromorphicOrderAt L 1 = ((-k₁ : ℤ) : WithTop ℤ) + meromorphicOrderAt G₁ 1 ∧
      meromorphicOrderAt (fun z => L z⁻¹) 0 =
        ((-kInf : ℤ) : WithTop ℤ) + meromorphicOrderAt BInf 0 := by
  intro F k₀ k₁ kInf B₀ A₁ G₁ aInf BInf
  obtain ⟨L, hL, hMer, hUp, h₀, h₁, hOrd₀, hOrd₁⟩ :=
    bbhh_actual_normalized_finite_plane M K H J P R Q S hP hQ hR hS
  obtain ⟨G, hG, hSlit⟩ := bbhh_b_slit_numerator H K M J R P Q S hR hQ hP hS
  obtain ⟨hBInf, hSeries, hDisk⟩ := bbhh_b_zero_series H K M J R P Q S hR hQ hP hS
  have hMatch (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hz₀ : z ≠ 0) : G z = -BInf z := by
    have heq := (hSlit z hz hz₀).unique (hDisk z hz hz₀)
    exact mul_left_cancel₀ (zpow_ne_zero _ hz₀) (by simpa only [BInf, neg_neg] using heq)
  let LInf (y : ℂ) := y ^ kInf * -(G y⁻¹)
  have hDchart : AnalyticOnNhd ℂ LInf U_D := by
    intro y hy
    have hy' : y ≠ 0 ∧ y⁻¹ ∈ slitDomain ∧ y⁻¹ ≠ 0 := hy
    exact (analyticAt_id.zpow hy'.1).mul (((hG _ hy'.2.1).comp (analyticAt_inv hy'.1)).neg)
  have hExtD (y : ℂ) (hy : 1 < ‖y‖) : y ∈ U_D := by
    rw [U_D_eq]
    intro h
    change y.im = 0 ∧ 0 ≤ y.re ∧ y.re ≤ 1 at h
    have hre : (y.re : ℂ) = y := Complex.ext rfl (by simpa using h.1.symm)
    have hnorm : ‖y‖ = y.re := calc
      ‖y‖ = ‖(y.re : ℂ)‖ := congrArg (fun z : ℂ => ‖z‖) hre.symm
      _ = y.re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.2.1]
    exact hy.not_ge (hnorm.symm ▸ h.2.2)
  have hInv (y : ℂ) (hy : 1 < ‖y‖) : y⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hy
  have hInfFormula (y : ℂ) (hy : 1 < ‖y‖) : LInf y = y ^ kInf * BInf y⁻¹ := by
    have hne : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hy)
    simp only [LInf, hMatch _ (hInv y hy) (inv_ne_zero hne), neg_neg]
  have hEq : EqOn L LInf U_D := by
    let y₀ : ℂ := (2 : ℂ) * I
    have hY : y₀ ∈ upperHalfPlane := by norm_num [y₀, upperHalfPlane, Complex.mul_im]
    have hY' : 1 < ‖y₀‖ := by norm_num [y₀, norm_mul]
    have hOpenU : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
    have hOpenE : IsOpen {y : ℂ | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have hA : AnalyticOnNhd ℂ L U_D := hL.mono U_D_subset_puncturedPlane
    refine hA.eqOn_of_preconnected_of_eventuallyEq hDchart isPreconnected_U_D (hExtD y₀ hY') ?_
    filter_upwards [hOpenU.eventually_mem hY, hOpenE.eventually_mem hY'] with y hu he
    have ha := normalized_bbhh_reversed_b M K H J P R Q S hP hQ hR hS hu he
    have hb := bbhh_b_infinity_series M K H J P R Q S hP hQ hR hS y he
    rw [hUp y hu, hInfFormula y he]
    simpa only [BInf, neg_neg, ← mul_neg] using congrArg Neg.neg (ha.unique hb)
  have hVal (y : ℂ) (hy : 1 < ‖y‖) : L y = y ^ kInf * BInf y⁻¹ :=
    (hEq (hExtD y hy)).trans (hInfFormula y hy)
  have hNear : (fun z => L z⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z ^ (-kInf) * BInf z := by
    have hBall : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball 0 1 := ball_mem_nhds 0 zero_lt_one
    filter_upwards [hBall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
    have hExt : 1 < ‖z⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hn)]
      exact mem_ball_zero_iff.mp hz
    simpa only [inv_zpow', inv_inv] using hVal z⁻¹ hExt
  have hOrd := meromorphic_order_of_cusp (-kInf) (t := fun z => z) analyticAt_id rfl
    (by simp) ((hBInf 0 (mem_ball_self zero_lt_one)).neg) hNear
  refine ⟨L, hL, hMer, hOrd.1, hUp, h₀, h₁, ?_, ?_, hOrd₀, hOrd₁, hOrd.2⟩
  · intro y hy
    refine ⟨?_, hVal y hy⟩
    rw [hVal y hy]
    simpa only [BInf, mul_neg, neg_neg] using
      bbhh_b_infinity_series M K H J P R Q S hP hQ hR hS y hy
  · intro z hz
    simpa only [BInf, neg_mul] using (hSeries z hz).neg

set_option maxHeartbeats 1700000 in
/-- A single polynomial numerator gives the normalized BBHH amplitude in all
three literal channels. The denominator powers depend on the sources only.
The polynomial is obtained from the finite Taylor readout of the cleared
reversed-product germ. -/
theorem bbhh_actual_normalized_common_rational (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let a₀ := (5 + H + K) / 2
    let a₁ := (M + H + 6) / 2
    let kInf : ℤ := (1 + (J : ℤ) - H) / 2
    let d := ((a₀ : ℤ) + a₁ + kInf).toNat
    let BInf (z : ℂ) := -energySum (bProductCoeff true true H M K J P Q R S) z
    let G (z : ℂ) := (z - 1) ^ a₁ * BInf z
    let p : Polynomial ℂ := ∑ n ∈ Finset.range (d + 1),
      Polynomial.C (coefficient n G) * Polynomial.X ^ (d - n)
    let f (y : ℂ) := p.eval y / (y ^ a₀ * (1 - y) ^ a₁)
    p.natDegree ≤ d ∧
    (∀ y ∈ upperHalfPlane, f y = bbhhNormalizedUpperAmplitude M K H J P R Q S y) ∧
    (∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 →
      HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
        (-f y)) ∧
    (∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
      HasSum (fun i => Complex.sqrt y *
        aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i) (f y)) ∧
    (∀ y : ℂ, 1 < ‖y‖ →
      HasSum (fun i => Complex.sqrt y * bJointTerm true true P Q R S (Complex.sqrt y) 1 i)
        (-f y)) := by
  classical
  intro a₀ a₁ kInf d BInf G p f
  obtain ⟨L, hHol, _, _, hUp, hB, hA, hD, _, _, _, _⟩ :=
    bbhh_actual_normalized_global_meromorphic M K H J P R Q S hP hQ hR hS
  have hG₀ := (bbhh_b_zero_series M K H J P R Q S hP hQ hR hS).1.neg
  have hG₁ := (bbhh_actual_normalized_collision_germ M K H J P R Q S hP hQ hR hS).1
  have hGInf := (bbhh_b_zero_series H K M J R P Q S hR hQ hP hS).1.neg
  let B₀ (y : ℂ) := -energySum (bProductCoeff true true M H K J R Q P S) y
  let A₁ (n : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H n) P R Q.val S.val
  let G₁ (y : ℂ) := Complex.sqrt y * (Complex.sqrt y ^ ((J : ℤ) - K) *
    energySum A₁ ((1 - y) / y))
  let E (y : ℂ) := if y = 0 then (1 - y) ^ a₁ * B₀ y else if y = 1 then y ^ a₀ * G₁ y
    else y ^ a₀ * (1 - y) ^ a₁ * L y
  have hCast₀ : (a₀ : ℤ) = (5 + (H : ℤ) + K) / 2 := by
    simp only [a₀, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hCast₁ : (a₁ : ℤ) = ((M : ℤ) + H + 6) / 2 := by
    simp only [a₁, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hCastD : (d : ℤ) = (a₀ : ℤ) + a₁ + kInf := by
    apply Int.toNat_of_nonneg
    dsimp only [kInf]
    omega
  have hCancel (y : ℂ) (a : ℕ) (hy : y ≠ 0) : y ^ a * y ^ (-(a : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hy, add_neg_cancel, zpow_zero]
  have hClear {y : ℂ} (h₀ : y ≠ 0) (h₁ : y ≠ 1) : E y = y ^ a₀ * (1 - y) ^ a₁ * L y := by
    simp only [E, ite_eq_right h₀, ite_eq_right h₁]
  have hSub (y : ℂ) : AnalyticAt ℂ (fun z : ℂ => 1 - z) y := analyticAt_const.sub analyticAt_id
  have hEntire : Differentiable ℂ E := by
    have hAt₀ : AnalyticAt ℂ E 0 := by
      have hball : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
      refine (((hSub 0).pow a₁).mul (hG₀ 0 hball)).congr ?_
      filter_upwards [isOpen_ball.eventually_mem hball] with y hy
      change (1 - y) ^ a₁ * B₀ y = E y
      by_cases hy₀ : y = 0
      · simp only [E, ite_eq_left hy₀]
      have hy₁ : y ≠ 1 := fun h => by simp [h] at hy
      rw [hClear hy₀ hy₁, (hB y hy hy₀).2, ← hCast₀]
      change (1 - y) ^ a₁ * B₀ y = y ^ a₀ * (1 - y) ^ a₁ * (y ^ (-(a₀ : ℤ)) * B₀ y)
      calc
        _ = (y ^ a₀ * y ^ (-(a₀ : ℤ))) * ((1 - y) ^ a₁ * B₀ y) := by
          rw [hCancel _ _ hy₀, one_mul]
        _ = _ := by ring
    have hAt₁ : AnalyticAt ℂ E 1 := by
      have ho : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
      have hOne : (1 : ℂ) ∈ rightHalf := by norm_num [rightHalf]
      refine ((analyticAt_id.pow a₀).mul (hG₁ 1 hOne)).congr ?_
      filter_upwards [ho.eventually_mem hOne] with y hy
      change y ^ a₀ * G₁ y = E y
      have hy₀ := right_ne_zero hy
      by_cases hy₁ : y = 1
      · dsimp only [E]
        rw [ite_eq_right hy₀, ite_eq_left hy₁]
      rw [hClear hy₀ hy₁, (hA y hy hy₁).2, ← hCast₁]
      change y ^ a₀ * G₁ y = y ^ a₀ * (1 - y) ^ a₁ * ((1 - y) ^ (-(a₁ : ℤ)) * G₁ y)
      calc
        _ = ((1 - y) ^ a₁ * (1 - y) ^ (-(a₁ : ℤ))) * (y ^ a₀ * G₁ y) := by
          rw [hCancel _ _ (sub_ne_zero.mpr (Ne.symm hy₁)), one_mul]
        _ = _ := by ring
    intro y
    by_cases hy₀ : y = 0
    · exact hy₀ ▸ hAt₀.differentiableAt
    by_cases hy₁ : y = 1
    · exact hy₁ ▸ hAt₁.differentiableAt
    have ho : IsOpen ({0, 1} : Set ℂ)ᶜ := (isClosed_singleton.union isClosed_singleton).isOpen_compl
    have hy : y ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hy₀, hy₁]
    apply AnalyticAt.differentiableAt
    refine (((analyticAt_id.pow a₀).mul ((hSub y).pow a₁)).mul (hHol y hy)).congr ?_
    filter_upwards [ho.eventually_mem hy] with z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa using hz
    exact (hClear hz'.1 hz'.2).symm
  have hG : AnalyticAt ℂ G 0 :=
    (((analyticAt_id (𝕜 := ℂ)).sub analyticAt_const).pow a₁).mul (hGInf 0 (mem_ball_self zero_lt_one))
  have hExterior : ∀ᶠ y in cobounded ℂ, E y = y ^ d * G y⁻¹ := by
    filter_upwards [tendsto_norm_cobounded_atTop (E := ℂ) |>.eventually_gt_atTop 1] with y hy
    have hy₀ := norm_pos_iff.mp (zero_lt_one.trans hy)
    have hy₁ : y ≠ 1 := fun h => by simp [h] at hy
    have hFactor : 1 - y = y * (y⁻¹ - 1) := by rw [mul_sub, mul_inv_cancel₀ hy₀, mul_one]
    have hPow : y ^ a₀ * y ^ a₁ * y ^ kInf = y ^ d := by
      rw [← pow_add, ← zpow_natCast, ← zpow_add₀ hy₀, Nat.cast_add, ← hCastD, zpow_natCast]
    rw [hClear hy₀ hy₁, (hD y hy).2, hFactor, mul_pow, ← hPow]
    change _ = _ * ((y⁻¹ - 1) ^ a₁ * BInf y⁻¹)
    ring
  have hEval (y : ℂ) : E y = p.eval y := by
    simpa only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using entire_eq_reversed_taylor hEntire hG hExterior y
  have hf (y : ℂ) (h₀ : y ≠ 0) (h₁ : y ≠ 1) : L y = f y := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ h₀)
      (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h₁))))).mpr
    rw [mul_comm, ← hClear h₀ h₁, hEval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro n _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le ..)
  · intro y hy
    have hy₀ : y ≠ 0 := fun h => by simp [upperHalfPlane, h] at hy
    have hy₁ : y ≠ 1 := fun h => by simp [upperHalfPlane, h] at hy
    exact (hf y hy₀ hy₁).symm.trans (hUp y hy)
  · intro y hy h₀
    have h₁ : y ≠ 1 := fun h => by simp [h] at hy
    rw [← hf y h₀ h₁]
    exact (hB y hy h₀).1
  · intro y hy h₁
    rw [← hf y (right_ne_zero hy) h₁]
    exact (hA y hy h₁).1
  · intro y hy
    have h₀ := norm_pos_iff.mp (zero_lt_one.trans hy)
    have h₁ : y ≠ 1 := fun h => by simp [h] at hy
    rw [← hf y h₀ h₁]
    exact (hD y hy).1

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHNormalizedGerm
