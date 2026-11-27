/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHBHDetectorReversal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHBHDetectorReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual mixed Leech BHBH crossing by finite detector reversal on a complex overlap. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalIterateInversion

/-! Actual double-mode sewing in the BHBH order via detector reversal. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Finset

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHDetectorReversal

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeMixedPairField (mu_coeff_even_zero)
open Orbifold.NativeMixedPairSkew (swapInput)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm b_joint_product_neg_root)
open NativeMixedPhysicalIterateInversion (a_joint_iterate_hasSum_detector_reversal)
open NativeMixedBProductInversion (b_joint_product_hasSum_detector_reversal)
open NativeHBHBArbitrarySewing (hbhb_actual_complex_sewing_of_states)

open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private mixed_a_off_diagonal aModeLinear aModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial
open private opposite_grade_parities bModeLinear bModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private BasisIndex ambientBasis basis_mem_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private BasisQuad component project_basis_val from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

/-- The HBHB coordinate chart parametrizing the reciprocal BHBH overlap. -/
def bhbhOverlap : Set ℂ := {y | 0 < y.im ∧ y.re < (1 / 2 : ℝ) ∧ 1 < ‖y‖}

theorem isOpen_bhbhOverlap : IsOpen bhbhOverlap :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const continuous_norm))

theorem bhbhOverlap_nonempty : bhbhOverlap.Nonempty := by
  refine ⟨(2 : ℂ) * I, ?_⟩
  norm_num [bhbhOverlap, Complex.mul_im, Complex.mul_re, norm_mul]

private theorem sqrt_re_pos_of_im_ne_zero {y : ℂ} (him : y.im ≠ 0) :
    0 < (Complex.sqrt y).re := by
  have hnonneg : 0 ≤ (Complex.sqrt y).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  refine lt_of_le_of_ne hnonneg ?_
  intro h
  apply him
  have hs := congrArg Complex.im (sqrt_square y).symm
  simpa only [pow_two, Complex.mul_im, ← h, zero_mul, mul_zero, add_zero] using hs

private theorem sqrt_mul_re_im (y : ℂ) :
    (Complex.sqrt y).re * (Complex.sqrt y).im +
      (Complex.sqrt y).im * (Complex.sqrt y).re = y.im := by
  simpa only [pow_two, Complex.mul_im] using congrArg Complex.im (sqrt_square y)

/-- The reciprocal roots lie in both radial domains. The ratio of the outer
and inner BHBH roots is the principal lift of `1 - y⁻¹`. Detector reversal has
separation root `1`, outer root `sqrt (1-y)`, and inner root `-I * sqrt y`. -/
theorem bhbh_reciprocal_roots {y : ℂ} (hy : y ∈ bhbhOverlap) :
    let xH := Complex.sqrt (1 - y)
    let zH := I * Complex.sqrt y
    let X := -zH⁻¹
    let Z := xH⁻¹
    let D := X * Z
    X ≠ 0 ∧ Z ≠ 0 ∧ D ≠ 0 ∧ ‖D‖ < ‖Z‖ ∧ ‖Z‖ < ‖X‖ ∧
      X ^ (2 : ℕ) = -y⁻¹ ∧ Z ^ (2 : ℕ) = (1 - y)⁻¹ ∧
      D ^ (2 : ℕ) = X ^ (2 : ℕ) - Z ^ (2 : ℕ) ∧
      X / Z = Complex.sqrt (1 - y⁻¹) ∧
      X = Z * (1 + (D / Z) ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹) ∧
      D / (X * Z) = 1 ∧ Z⁻¹ = xH ∧ X⁻¹ = -zH := by
  obtain ⟨him, hre, hnorm⟩ := hy
  let xH := Complex.sqrt (1 - y)
  let zH := I * Complex.sqrt y
  let X := -zH⁻¹
  let Z := xH⁻¹
  let D := X * Z
  have hy₀ : y ≠ 0 := by
    intro h
    simp [h] at him
  have hcyim : (1 - y).im < 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_lt_zero] using him
  have hxre : 0 < xH.re := sqrt_re_pos_of_im_ne_zero (ne_of_lt hcyim)
  have hyre : 0 < (Complex.sqrt y).re := sqrt_re_pos_of_im_ne_zero (ne_of_gt him)
  have hxim : xH.im ≤ 0 := by
    change (Complex.sqrt (1 - y)).im ≤ 0
    rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt hcyim]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hyim : 0 < (Complex.sqrt y).im := by
    by_contra! hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hyre.le hn
    have hm' := mul_nonpos_of_nonpos_of_nonneg hn hyre.le
    linarith [sqrt_mul_re_im y]
  have hzre : 0 < (-zH).re := by
    simpa only [zH, Complex.neg_re, Complex.I_mul_re, neg_neg] using hyim
  have hzim : (-zH).im ≤ 0 := by
    simpa only [zH, Complex.neg_im, Complex.I_mul_im] using neg_nonpos.mpr hyre.le
  have hx₀ : xH ≠ 0 := by
    intro h
    simp [h] at hxre
  have hz₀ : zH ≠ 0 := by
    intro h
    simp [h] at hzre
  have hX : X ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz₀)
  have hZ : Z ≠ 0 := inv_ne_zero hx₀
  have hD : D ≠ 0 := mul_ne_zero hX hZ
  have hxSq : xH ^ (2 : ℕ) = 1 - y := sqrt_square _
  have hzSq : zH ^ (2 : ℕ) = -y := by
    rw [show zH = I * Complex.sqrt y from rfl, mul_pow, Complex.I_sq, sqrt_square, neg_one_mul]
  have hkx : ‖xH‖ ^ (2 : ℕ) = ‖1 - y‖ := by rw [← norm_pow, hxSq]
  have hkz : ‖zH‖ ^ (2 : ℕ) = ‖y‖ := by rw [← norm_pow, hzSq, norm_neg]
  have hrad₁ : 1 < ‖zH‖ := by
    apply (sq_lt_sq₀ zero_le_one (norm_nonneg zH)).mp
    simpa only [one_pow, hkz] using hnorm
  have hnormDiff : ‖y‖ < ‖1 - y‖ := by
    have h : (1 / 2 : ℝ) < (1 - y).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    simpa only [sub_sub_cancel] using (norm_one_sub_lt_iff (1 - y)).mpr h
  have hrad₂ : ‖zH‖ < ‖xH‖ := by
    apply (sq_lt_sq₀ (norm_nonneg zH) (norm_nonneg xH)).mp
    simpa only [hkx, hkz] using hnormDiff
  have hXrad : ‖X‖ < 1 := by
    simpa only [X, norm_neg, norm_inv, inv_one] using
      (inv_lt_inv₀ (norm_pos_iff.mpr hz₀) zero_lt_one).mpr hrad₁
  have hArad : ‖D‖ < ‖Z‖ := by
    simpa only [D, norm_mul, one_mul] using
      mul_lt_mul_of_pos_right hXrad (norm_pos_iff.mpr hZ)
  have hBrad : ‖Z‖ < ‖X‖ := by
    simpa only [Z, X, norm_neg, norm_inv] using
      (inv_lt_inv₀ (norm_pos_iff.mpr hx₀) (norm_pos_iff.mpr hz₀)).mpr hrad₂
  have hratio : X / Z = xH / (-zH) := by
    simp only [X, Z, div_eq_mul_inv, inv_inv, inv_neg, mul_comm]
  have hrre : 0 < (X / Z).re := by
    have hden : 0 < Complex.normSq (-zH) := Complex.normSq_pos.mpr (neg_ne_zero.mpr hz₀)
    rw [hratio, div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    exact sub_pos.mpr (lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg hxim (div_nonneg (neg_nonneg.mpr hzim) hden.le))
      (mul_pos hxre (div_pos hzre hden)))
  have hratioSq : (X / Z) ^ (2 : ℕ) = 1 - y⁻¹ := by
    rw [hratio, div_pow, neg_sq, hxSq, hzSq]
    field_simp [hy₀]
    ring
  have hprincipal : X / Z = Complex.sqrt (1 - y⁻¹) := by
    rw [Complex.sqrt, ← hratioSq, Complex.sq_cpow_two_inv hrre]
  have hDZ : D / Z = X := mul_div_cancel_right₀ X hZ
  have hXSq : X ^ (2 : ℕ) = -y⁻¹ := by
    rw [show X = -zH⁻¹ from rfl, neg_sq, inv_pow, hzSq, inv_neg]
  have hZSq : Z ^ (2 : ℕ) = (1 - y)⁻¹ := by
    rw [show Z = xH⁻¹ from rfl, inv_pow, hxSq]
  have hRel : (1 + (D / Z) ^ (2 : ℕ)) = (X / Z) ^ (2 : ℕ) := by
    rw [hDZ, hXSq, hratioSq, sub_eq_add_neg]
  have hLift : X = Z * (1 + (D / Z) ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹) := by
    rw [hRel, Complex.sq_cpow_two_inv hrre, mul_comm]
    exact (div_mul_cancel₀ X hZ).symm
  have hDiff : D ^ (2 : ℕ) = X ^ (2 : ℕ) - Z ^ (2 : ℕ) := by
    have hcancel (a : ℂ) : (a / Z) ^ (2 : ℕ) * Z ^ (2 : ℕ) = a ^ (2 : ℕ) := by
      rw [← mul_pow, div_mul_cancel₀ _ hZ]
    have hscaled := congrArg (fun a : ℂ => a * Z ^ (2 : ℕ)) hRel
    change (1 + (D / Z) ^ (2 : ℕ)) * Z ^ (2 : ℕ) =
      (X / Z) ^ (2 : ℕ) * Z ^ (2 : ℕ) at hscaled
    rw [add_mul, one_mul, hcancel D, hcancel X] at hscaled
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hscaled)
  exact ⟨hX, hZ, hD, hArad, hBrad, hXSq, hZSq, hDiff, hprincipal, hLift,
    div_self hD, inv_inv xH, by simp only [inv_neg, inv_inv]⟩

private theorem hbhb_a_tsum_neg_root (M K L N : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hw : w.val ∈ actualGrade ℒ leechUnit K)
    (hv : v.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (d z : ℂ) :
    (∑' p, aJointTerm false u w v.val b.val d (-z) p) =
      -(∑' p, aJointTerm false u w v.val b.val d z p) := by
  by_cases hzero : u = 0 ∨ w = 0 ∨ v = 0 ∨ b = 0
  · rcases hzero with rfl | rfl | rfl | rfl
    · simp [← aModeLinear_apply false false]
    · simp [← aModeLinear_apply false false]
    · simp [aJointTerm]
    · simp [aJointTerm]
  push Not at hzero
  obtain ⟨hu₀, hw₀, hv₀, hb₀⟩ := hzero
  have hinner := (opposite_grade_parities u w hu hw hu₀ hw₀).1
  have houter := (opposite_grade_parities v b hv hb hv₀ hb₀).2
  rw [← tsum_neg]
  apply tsum_congr
  intro p
  by_cases he : Even p.2
  · by_cases hj : Even p.1
    · simp [aJointTerm, mu_coeff_even_zero false _ u w hj]
    · have hoff : p.2 ≠ (N : ℤ) - L - (p.1 + (M : ℤ) + K + 6) := by
        obtain ⟨a, ha⟩ := hinner
        obtain ⟨c, hc⟩ := houter
        obtain ⟨j, hj'⟩ := Int.not_even_iff_odd.mp hj
        obtain ⟨e, he'⟩ := he
        omega
      have hc := mixed_a_off_diagonal false M K L N u w v.val b.val
        hu hw hv hb hinner p.1 p.2 hoff
      simp only [aJointTerm, hc, zero_mul, neg_zero]
  · have ho := Int.not_even_iff_odd.mp he
    simp only [aJointTerm, ho.neg_zpow, mul_neg]

set_option maxHeartbeats 4000000 in
-- Elaborates both detector reversals and matches their nested finite sums.
/-- Actual BHBH crossing for homogeneous states on the reciprocal root lift.
Both literal double sums converge, with the same value. The two reversal
formulas pair the same descendants against the same detector, with the same
phase and coordinate powers. -/
theorem bhbh_actual_complex_sewing_of_homogeneous (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ bhbhOverlap) :
    let X := -(I * Complex.sqrt y)⁻¹
    let Z := (Complex.sqrt (1 - y))⁻¹
    let A := aJointTerm true P Q R.val S.val (X * Z) Z
    let B := bJointTerm false true Q R P S X Z
    HasSum A (∑' p, B p) ∧ HasSum B (∑' p, B p) ∧ (∑' p, A p) = ∑' p, B p := by
  let xH := Complex.sqrt (1 - y)
  let zH := I * Complex.sqrt y
  let X := -zH⁻¹
  let Z := xH⁻¹
  let D := X * Z
  obtain ⟨hX, hZ, hD, hradA, hradB, _, _, _, _, hLift, hd', hx', hz'⟩ :=
    bhbh_reciprocal_roots hy
  change D / (X * Z) = 1 at hd'
  change Z⁻¹ = xH at hx'
  change X⁻¹ = -zH at hz'
  have ha := a_joint_iterate_hasSum_detector_reversal true true M K H J P Q R S
    hP hQ hR hS (d := D) (x := X) (z := Z) hD hradA hLift
  have hb := b_joint_product_hasSum_detector_reversal false true M K H J Q R P S
    hQ hR hP hS (xR := X) (zR := Z) hX hZ hradB
  rw [hd', hz'] at ha
  rw [hx', hz'] at hb
  have hswapOdd (w : TwistedOdd) : swapInput (s := true) w = w := Subtype.ext rfl
  have hswapEven (v : TwistedEven) : swapInput (s := false) v = v := Subtype.ext rfl
  simp only [hswapOdd] at ha
  have hdesc (i j : ℕ) (hi : i ∈ Finset.range (M / 2 + 1))
      (hj : j ∈ Finset.range (K / 2 + 1)) :
      (∑' p, aJointTerm false ((L₁ false ^ j) Q) ((L₁ true ^ i) P)
        S.val R.val 1 (-zH) p) =
      ∑' p, bJointTerm true false ((L₁ true ^ i) P) S ((L₁ false ^ j) Q) R xH (-zH) p := by
    have hi' : i ≤ M / 2 := by simpa using hi
    have hj' : j ≤ K / 2 := by simpa using hj
    have hPi := lowered_grade (s := true) (u := P) hP hi'
    have hQj := lowered_grade (s := false) (u := Q) hQ hj'
    have hc := (hbhb_actual_complex_sewing_of_states ((L₁ false ^ j) Q) S
      ((L₁ true ^ i) P) R hy.1 hy.2.1 hy.2.2).2.2
    change (∑' p, aJointTerm false ((L₁ false ^ j) Q) ((L₁ true ^ i) P) S.val R.val 1 zH p) =
      (∑' p, bJointTerm true false ((L₁ true ^ i) P) (swapInput (s := false) S)
        ((L₁ false ^ j) Q) R xH zH p) at hc
    rw [hswapEven] at hc
    rw [hbhb_a_tsum_neg_root (K - 2 * j) (M - 2 * i) J H _ _ _ _
      hQj hPi hS hR, b_joint_product_neg_root, hc]
  let c (i j : ℕ) : ℂ :=
    ((i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹) *
      (X ^ (2 * (i : ℤ) - 6 - 2 * (M : ℤ)) * Z ^ (2 * (j : ℤ) - 6 - 2 * (K : ℤ)))
  let V : ℂ := I ^ ((M : ℤ) - K) * ∑ i ∈ Finset.range (M / 2 + 1),
    ∑ j ∈ Finset.range (K / 2 + 1), c i j *
      ∑' p, bJointTerm true false ((L₁ true ^ i) P) S ((L₁ false ^ j) Q) R xH (-zH) p
  have hvalue :
      I ^ ((M : ℤ) - K) * (∑ i ∈ Finset.range (M / 2 + 1),
        ∑ j ∈ Finset.range (K / 2 + 1), c i j *
          ∑' p, aJointTerm false ((L₁ false ^ j) Q) ((L₁ true ^ i) P)
            S.val R.val 1 (-zH) p) = V := by
    unfold V
    apply congrArg (fun a : ℂ => I ^ ((M : ℤ) - K) * a)
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [hdesc i j hi hj]
  let A := aJointTerm true P Q R.val S.val D Z
  let B := bJointTerm false true Q R P S X Z
  have hA : HasSum A V := by
    rw [← hvalue]
    exact ha
  have hB : HasSum B V := hb
  change HasSum A (∑' p, B p) ∧ HasSum B (∑' p, B p) ∧ (∑' p, A p) = ∑' p, B p
  rw [hB.tsum_eq]
  exact ⟨hA, hB, hA.tsum_eq⟩

private abbrev BHBHLinear :=
  TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ

private def aMode (X Z : ℂ) (p : ℤ × ℤ) : BHBHLinear :=
  aModeLinear true true (X * Z) Z p

private theorem aMode_apply (X Z : ℂ) (p : ℤ × ℤ)
    (P R : TwistedOdd) (Q S : TwistedEven) :
    aMode X Z p P Q R S = aJointTerm true P Q R.val S.val (X * Z) Z p :=
  aModeLinear_apply true true (X * Z) Z p P Q R S

private def bMode (X Z : ℂ) (p : ℤ × ℤ) : BHBHLinear :=
  let swap : (TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  (swap.comp (bModeLinear false true X Z p)).flip

private theorem bMode_apply (X Z : ℂ) (p : ℤ × ℤ)
    (P R : TwistedOdd) (Q S : TwistedEven) :
    bMode X Z p P Q R S = bJointTerm false true Q R P S X Z p :=
  bModeLinear_apply false true X Z p Q R P S

private theorem component_grade (s : Bool) (u : Twisted ℒ leechUnit s) (i : BasisIndex) :
    (component s u i).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  change (ambientBasis.repr u.val i • project s (ambientBasis i)).val ∈ _
  rw [Submodule.coe_smul, project_basis_val]
  apply Submodule.smul_mem
  split_ifs <;> first | exact basis_mem_grade i | exact Submodule.zero_mem _

private def basisTuples (P R : TwistedOdd) (Q S : TwistedEven) : Finset BasisQuad :=
  (ambientBasis.repr P.val).support ×ˢ ((ambientBasis.repr Q.val).support ×ˢ
    ((ambientBasis.repr R.val).support ×ˢ (ambientBasis.repr S.val).support))

private abbrev onComponents (P R : TwistedOdd) (Q S : TwistedEven)
    (F : BHBHLinear) (i : BasisQuad) : ℂ :=
  F (component true P i.1) (component false Q i.2.1)
    (component true R i.2.2.1) (component false S i.2.2.2)

private theorem expand (P R : TwistedOdd) (Q S : TwistedEven) (F : BHBHLinear) :
    F P Q R S = ∑ i ∈ basisTuples P R Q S, onComponents P R Q S F i := by
  classical
  conv_lhs =>
    rw [← sum_projectedBasis true P]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis false Q]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis true R]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis false S]
    simp only [map_sum]
  simp only [basisTuples, Finset.sum_product]

set_option maxHeartbeats 4000000 in
-- Elaborates four-variable linear maps and the finite expansion of both native series.
/-- Actual BHBH crossing for arbitrary states on the reciprocal root lift.
The common value follows by finite expansion in the projected homogeneous
basis. -/
theorem bhbh_actual_complex_sewing_of_states
    (P R : TwistedOdd) (Q S : TwistedEven) {y : ℂ} (hy : y ∈ bhbhOverlap) :
    let X := -(I * Complex.sqrt y)⁻¹
    let Z := (Complex.sqrt (1 - y))⁻¹
    let A := aJointTerm true P Q R.val S.val (X * Z) Z
    let B := bJointTerm false true Q R P S X Z
    HasSum A (∑' p, B p) ∧ HasSum B (∑' p, B p) ∧ (∑' p, A p) = ∑' p, B p := by
  classical
  let X := -(I * Complex.sqrt y)⁻¹
  let Z := (Complex.sqrt (1 - y))⁻¹
  let A := aMode X Z
  let B := bMode X Z
  let value (i : BasisQuad) := ∑' p, onComponents P R Q S (B p) i
  have hcomponent (i : BasisQuad) :
      HasSum (fun p => onComponents P R Q S (A p) i) (value i) ∧
      HasSum (fun p => onComponents P R Q S (B p) i) (value i) := by
    have h := bhbh_actual_complex_sewing_of_homogeneous
      (oddWeight ℒ i.1.1) (oddWeight ℒ i.2.1.1)
      (oddWeight ℒ i.2.2.1.1) (oddWeight ℒ i.2.2.2.1)
      (component true P i.1) (component true R i.2.2.1)
      (component false Q i.2.1) (component false S i.2.2.2)
      (component_grade true P i.1) (component_grade false Q i.2.1)
      (component_grade true R i.2.2.1) (component_grade false S i.2.2.2) hy
    simpa only [value, onComponents, A, B, aMode_apply, bMode_apply, X, Z] using
      And.intro h.1 h.2.1
  let V := ∑ i ∈ basisTuples P R Q S, value i
  have hA : HasSum (fun p => A p P Q R S) V := by
    refine (hasSum_sum (s := basisTuples P R Q S) fun i _ => (hcomponent i).1).congr_fun ?_
    exact fun p => expand P R Q S (A p)
  have hB : HasSum (fun p => B p P Q R S) V := by
    refine (hasSum_sum (s := basisTuples P R Q S) fun i _ => (hcomponent i).2).congr_fun ?_
    exact fun p => expand P R Q S (B p)
  have hBoth : HasSum (fun p => A p P Q R S) (∑' p, B p P Q R S) ∧
      HasSum (fun p => B p P Q R S) (∑' p, B p P Q R S) ∧
      (∑' p, A p P Q R S) = ∑' p, B p P Q R S := by
    rw [hB.tsum_eq]
    exact ⟨hA, hB, hA.tsum_eq⟩
  simpa only [A, B, aMode_apply, bMode_apply, X, Z] using hBoth

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHDetectorReversal
