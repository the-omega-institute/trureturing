/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHNonzeroComparison
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHNonzeroComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonzero ground-state test of the actual Leech four-H overlap. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The vacuum term and the comparison of the native A iterate and B product
for weight-`3/2` states in the even Leech twisted sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped TensorProduct VertexOperator
open Set Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHNonzeroComparison

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open Complex (I)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualGround groundRank)
open LatticeHalfFockGradedTrace (actualGrade actualAmbientBasis
  actual_grade_mem_iff_repr_support oddWeight)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open LatticeInvolution (fixedVacuum)
open LatticeTwistedGroundRealization (Half)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven leechUnit paritySign)
open Orbifold.NativeFixedPairField (nu_ground_vacuum)
open Orbifold.NativeFixedUpperRightSkew (rightField rightField_coeff R_vacuum)
open NativeFourHUpperProduct (fixedBProductCoeff fixedBProductCoeff_eq_slit_taylor
  fixedBProduct_hasSum)
open NativeMixedUpperProductCusp (bSewnNumerator)
open NativeFixedPairAIterate (fixedAIterateCoeff)
open NativeMixedWickChartTransport (laurentRoot sigma)
open OriginalGaussianSewnAnalytic (coefficient)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (ball_subset_slitDomain)

open private selectedGroundPairing actualForm_tmul from
  D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private bSewnNumerator_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHUpperProduct

local notation "ℒ" => leechData
private abbrev Ground := ActualGround ℒ leechUnit
private abbrev IsGround (u : TwistedEven) : Prop := u.val ∈ actualGrade ℒ leechUnit 0

private theorem groundTensor_grade (g : Ground) :
    (1 ⊗ₜ[ℂ] g) ∈ actualGrade ℒ leechUnit 0 := by
  classical
  apply (actual_grade_mem_iff_repr_support ℒ leechUnit 0 _).mpr
  rintro ⟨d, j⟩ hj
  have hc := Finsupp.mem_support_iff.mp hj
  change (actualAmbientBasis ℒ leechUnit).repr (1 ⊗ₜ[ℂ] g) (d, j) ≠ 0 at hc
  have hrepr : (actualAmbientBasis ℒ leechUnit).repr (1 ⊗ₜ[ℂ] g) (d, j) =
      g j * (1 : Oscillator ℒ).coeff d := by
    unfold actualAmbientBasis
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    rfl
  rw [hrepr, MvPolynomial.coeff_one] at hc
  by_cases hd : 0 = d
  · simp [← hd, oddWeight]
  · exact (hc (by rw [ite_eq_right hd, mul_zero])).elim

private def groundState (g : Ground) : TwistedEven :=
  ⟨1 ⊗ₜ[ℂ] g, by
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, paritySign, Bool.false_eq_true, ↓reduceIte, pow_zero,
      one_smul] using actualParity_on_actualGrade ℒ leechUnit 0
      ⟨1 ⊗ₜ[ℂ] g, groundTensor_grade g⟩⟩

private theorem exists_ordered_ground_pair :
    ∃ p d : Ground, actualForm ℒ leechUnit (groundState d).val (groundState p).val = 1 := by
  classical
  let G := selectedGroundPairing ℒ leechUnit
  let b := Pi.basisFun ℂ (Half (groundRank ℒ leechUnit))
  let j : Half (groundRank ℒ leechUnit) := 0
  refine ⟨b j, G.form.dualBasis G.nondegenerate b j, ?_⟩
  change actualForm ℒ leechUnit (1 ⊗ₜ[ℂ] G.form.dualBasis G.nondegenerate b j)
    (1 ⊗ₜ[ℂ] b j) = 1
  have hwick : SignedOscillatorWick.wick ℒ 1 1 = 1 := by
    simpa [MvPolynomial.coeff_one]
      using SignedOscillatorWick.wick_constant_left ℒ 1 1
  rw [actualForm_tmul, hwick, mul_one]
  simpa using G.form.apply_dualBasis_left G.nondegenerate b j j

/-- The B energy-zero coefficient reads the ordered ground pairings through
the actual even pair field at doubled exponent `-6` and the right field at
doubled exponent `0` (physical mode `-1`). -/
theorem fixedBProductCoeff_ground_zero (u v w b : TwistedEven)
    (hv : v.val ∈ actualGrade ℒ leechUnit 0) (hw : w.val ∈ actualGrade ℒ leechUnit 0) :
    fixedBProductCoeff false false 0 0 0 0 v w u b 0 =
      I * actualForm ℒ leechUnit w.val v.val * actualForm ℒ leechUnit b.val u.val := by
  change actualForm ℒ leechUnit b.val
    ((rightField ℒ leechUnit false u).coeff 0 ((Orbifold.NativeFixedPairField.nu false v).coeff
      (-6) w)).val = _
  rw [nu_ground_vacuum v w hv hw, map_smul,
    show (0 : ℤ) = -2 * (-1) - 2 by decide, rightField_coeff,
    R_vacuum ℒ leechUnit false (-1) (le_refl _) u, ite_eq_left rfl]
  simp only [Submodule.coe_smul, map_smul, smul_eq_mul]

private theorem ground_numerator_zero (p d : Ground)
    (hpair : actualForm ℒ leechUnit (groundState d).val (groundState p).val = 1) :
    bSewnNumerator 0 0 0 1 1 1 1 p p d d 0 = 1 := by
  let u := groundState p
  let b := groundState d
  have hu : IsGround u := groundTensor_grade p
  have hb : IsGround b := groundTensor_grade d
  have hE : Even (0 : ℤ) := ⟨0, rfl⟩
  have h0 := fixedBProductCoeff_eq_slit_taylor false false 0 0 0 0 u b u b 1 1 1 1 p p d d
    hu hb hu hb rfl rfl rfl rfl hE hE 0
  rw [fixedBProductCoeff_ground_zero u u b b hu hb, hpair, mul_one, mul_one] at h0
  change I = I ^ (-3 : ℤ) * coefficient 0 (bSewnNumerator 0 0 0 1 1 1 1 p p d d) at h0
  have hphase : I ^ (-3 : ℤ) = I := by
    rw [show (-3 : ℤ) = 1 - 4 by decide, zpow_sub₀ Complex.I_ne_zero, zpow_one,
      show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast, Complex.I_pow_four, div_one]
  have hconstant :
      coefficient 0 (bSewnNumerator 0 0 0 1 1 1 1 p p d d) =
        bSewnNumerator 0 0 0 1 1 1 1 p p d d 0 := by simp [coefficient]
  rw [hphase, hconstant] at h0
  exact mul_left_cancel₀ Complex.I_ne_zero ((mul_one I).trans h0) |>.symm

private theorem exists_nonzero_ground_numerator (p d : Ground)
    (hpair : actualForm ℒ leechUnit (groundState d).val (groundState p).val = 1) :
    ∃ y : ℝ, (1 / 2 : ℝ) < y ∧ y < 1 ∧ bSewnNumerator 0 0 0 1 1 1 1 p p d d y ≠ 0 := by
  let F := bSewnNumerator 0 0 0 1 1 1 1 p p d d
  have hdiff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) :=
    (bSewnNumerator_differentiableOn 0 0 0 1 1 1 1 p p d d).mono ball_subset_slitDomain
  by_contra! h
  change ∀ y : ℝ, (1 / 2 : ℝ) < y → y < 1 → F y = 0 at h
  let a : ℝ := 1 / 2
  let S : Set ℝ := Ioc a (3 / 4)
  have ha : a ∈ closure S := by
    dsimp only [S, a]
    rw [closure_Ioc (by norm_num : (1 / 2 : ℝ) ≠ 3 / 4)]
    exact ⟨le_rfl, by norm_num⟩
  have hsub : Complex.ofReal '' S ⊆ {z | F z = 0} \ {(a : ℂ)} := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨h y hy.1 (hy.2.trans_lt (by norm_num)),
      fun hya => hy.1.ne' (Complex.ofReal_injective (mem_singleton_iff.mp hya))⟩
  have hac : (a : ℂ) ∈ closure ({z | F z = 0} \ {(a : ℂ)}) :=
    closure_mono hsub (mem_closure_image Complex.continuous_ofReal.continuousAt ha)
  have haball : (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    norm_num [a]
  have hzero := (hdiff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_ball haball hac (mem_ball_self zero_lt_one : (0 : ℂ) ∈ ball 0 1)
  exact one_ne_zero ((ground_numerator_zero p d hpair).symm.trans hzero)

/-- A ground state and its ordered dual give an unconditional nonzero test
of the actual four-H overlap. Here A uses the native Laurent root and B uses
the positive root in the physical energy series. The chart factor is
`y^3`, so the constant scalar on this normalized comparison is unique. -/
theorem fourH_ground_nonzero_comparison :
    ∃ u b : TwistedEven,
      u.val ∈ actualGrade ℒ leechUnit 0 ∧ b.val ∈ actualGrade ℒ leechUnit 0 ∧
      actualForm ℒ leechUnit b.val u.val = 1 ∧
      fixedBProductCoeff false false 0 0 0 0 u b u b 0 = I ∧
      let A := fun (y : ℝ) (j : ℤ) =>
        fixedAIterateCoeff false 0 0 0 0 j u u b.val b.val * laurentRoot .A y ^ j
      let B := fun (y : ℝ) (E : ℕ) =>
        fixedBProductCoeff false false 0 0 0 0 u b u b E *
          (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - 6)
      (∀ y : ℝ, (1 / 2 : ℝ) < y → y < 1 →
        Summable (A y) ∧ Summable (B y) ∧
        (∑' j, A y j) = (y : ℂ) ^ (3 : ℤ) * ∑' E, B y E) ∧
      (∃ y : ℝ, (1 / 2 : ℝ) < y ∧ y < 1 ∧ (∑' E, B y E) ≠ 0) ∧
      ∀ c : ℂ, (∀ y : ℝ, (1 / 2 : ℝ) < y → y < 1 →
        (∑' j, A y j) = c * ((y : ℂ) ^ (3 : ℤ) * ∑' E, B y E)) ↔ c = 1 := by
  obtain ⟨p, d, hpair⟩ := exists_ordered_ground_pair
  let u := groundState p
  let b := groundState d
  have hu : IsGround u := groundTensor_grade p
  have hb : IsGround b := groundTensor_grade d
  refine ⟨u, b, hu, hb, hpair, ?_, ?_⟩
  · rw [fixedBProductCoeff_ground_zero u u b b hu hb, hpair, mul_one, mul_one]
  let A := fun (y : ℝ) (j : ℤ) =>
    fixedAIterateCoeff false 0 0 0 0 j u u b.val b.val * laurentRoot .A y ^ j
  let B := fun (y : ℝ) (E : ℕ) =>
    fixedBProductCoeff false false 0 0 0 0 u b u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - 6)
  have hcompare (y : ℝ) (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
      Summable (A y) ∧ Summable (B y) ∧
      (∑' j, A y j) = (y : ℂ) ^ (3 : ℤ) * ∑' E, B y E := by
    have hσ : sigma 0 0 0 0 = 3 := by norm_num [sigma]
    simpa only [A, B, Nat.cast_zero, add_zero, hσ]
      using NativeFourHHomogeneousExtension.fourH_actual_A_eq_B_of_homogeneous
        0 0 0 0 u u b b hu hu hb hb hy hy₁
  obtain ⟨y, hy, hy₁, hF⟩ := exists_nonzero_ground_numerator p d hpair
  have hy₀ : 0 < y := (by norm_num : (0 : ℝ) < 1 / 2).trans hy
  have hroot : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy₀).ne'
  have hE : Even (0 : ℤ) := ⟨0, rfl⟩
  have hsum := fixedBProduct_hasSum false false 0 0 0 0 u b u b 1 1 1 1 p p d d
    hu hb hu hb rfl rfl rfl rfl hE hE hy₀ hy₁
  have hB : (∑' E, B y E) ≠ 0 := by
    change HasSum (B y)
      ((I * (Real.sqrt y : ℂ)) ^ (-6 : ℤ) * I ^ (3 : ℤ) *
        bSewnNumerator 0 0 0 1 1 1 1 p p d d y) at hsum
    rw [hsum.tsum_eq]
    exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (mul_ne_zero Complex.I_ne_zero hroot))
      (zpow_ne_zero _ Complex.I_ne_zero)) hF
  refine ⟨hcompare, ⟨y, hy, hy₁, hB⟩, fun c => ⟨?_, ?_⟩⟩
  · intro h
    have hs : (y : ℂ) ^ (3 : ℤ) * ∑' E, B y E ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr hy₀.ne')) hB
    have heq := (h y hy hy₁).symm.trans (hcompare y hy hy₁).2.2
    exact mul_right_cancel₀ hs (heq.trans (one_mul _).symm)
  · rintro rfl x hx hx₁
    simpa only [one_mul] using (hcompare x hx hx₁).2.2

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHNonzeroComparison
