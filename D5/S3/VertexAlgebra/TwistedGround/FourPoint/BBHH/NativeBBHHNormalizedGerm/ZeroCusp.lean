import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHUpperCrossing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBPolynomialFromInfinity

/-! The normalized BBHH amplitude and its native Laurent expansion at zero. -/

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
open NativeFixedPairAIterate
  (fixedAExponent fixedAIterateCoeff fixedAIterateCoeff_eq_zero_off_energy)
open NativeMixedUpperProductCusp
  (bJointTerm bProductCoeff b_joint_product_hasSum bSewnNumerator)
open Orbifold.NativeFullMixedField (project)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain isOpen_slitDomain ball_subset_slitDomain)
open NativeMixedProductSlot23PhysicalRoots (b_joint_product_hasSum_scale)

open private physical_roots eval_translation_inverse from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHUpperCrossing
open private source_roots reversal_roots from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation
open private bEnergyTerm bEnergy_hasSum_iff bModeLinear bModeLinear_apply opposite_grade_parities from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private bEnergyTerm_factor bProductCoeff_summable_on_disk from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic
open private energySum energySum_analyticAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private sqrt_square zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open OriginalFourPointChartGluing (U_D U_D_eq)
open OriginalGaussianSewnAnalytic (coefficient)

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

theorem normalized_bbhh_b (M K H J : ℕ)
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

theorem analytic_normalized_bbhh (M K H J : ℕ)
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

theorem bbhh_b_zero_series (M K H J : ℕ)
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

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHNormalizedGerm
