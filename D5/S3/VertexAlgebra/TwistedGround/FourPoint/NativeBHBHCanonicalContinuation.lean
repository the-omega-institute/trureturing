/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHBHCanonicalContinuation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic finite reciprocal amplitude for actual BHBH states. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBCanonicalContinuation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHDetectorReversal

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeMixedPairSkew (swapInput)
open NativeHBHBCanonicalContinuation (upperHalfPlane hbhbUpperAmplitude hbhbUpperAmplitude_spec)
open NativeHBHBUpperCrossing (upperTransportDomain)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm b_joint_product_neg_root)
open NativeMixedPhysicalIterateInversion (a_joint_iterate_hasSum_detector_reversal)
open NativeMixedBProductInversion (b_joint_product_hasSum_detector_reversal)

open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private sqrt_re_pos_of_im_ne_zero sqrt_mul_re_im hbhb_a_tsum_neg_root from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHDetectorReversal
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

/-- Outer reciprocal root, equal to `I / sqrt y`. -/
def outerRoot (y : ℂ) : ℂ := -(I * Complex.sqrt y)⁻¹

/-- Inner reciprocal root. The separation root is their product. -/
def innerRoot (y : ℂ) : ℂ := (Complex.sqrt (1 - y))⁻¹

theorem outerRoot_eq (y : ℂ) : outerRoot y = I / Complex.sqrt y := by
  rw [outerRoot, mul_inv_rev, Complex.inv_I, mul_neg, neg_neg, div_eq_mul_inv, mul_comm]

private theorem source_roots {y : ℂ} (him : 0 < y.im) :
    AnalyticAt ℂ Complex.sqrt y ∧
    AnalyticAt ℂ (fun z => Complex.sqrt (1 - z)) y ∧
    Complex.sqrt y ≠ 0 ∧ Complex.sqrt (1 - y) ≠ 0 := by
  have hcy : (1 - y).im < 0 := by simpa using neg_neg_of_pos him
  have hslit : y ∈ Complex.slitPlane := Or.inr (ne_of_gt him)
  have hcslit : 1 - y ∈ Complex.slitPlane := Or.inr (ne_of_lt hcy)
  have ha (z : ℂ) (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ Complex.sqrt z := by
    unfold Complex.sqrt
    exact analyticAt_id.cpow analyticAt_const hz
  refine ⟨ha y hslit, (ha (1 - y) hcslit).comp (analyticAt_const.sub analyticAt_id), ?_, ?_⟩
  · exact ne_of_apply_ne Complex.re (by simpa using (sqrt_re_pos_of_im_ne_zero (ne_of_gt him)).ne')
  · exact ne_of_apply_ne Complex.re (by simpa using (sqrt_re_pos_of_im_ne_zero (ne_of_lt hcy)).ne')

private theorem reversal_roots {y : ℂ} (him : 0 < y.im) :
    let X := outerRoot y
    let Z := innerRoot y
    X ≠ 0 ∧ Z ≠ 0 ∧ (X * Z) / (X * Z) = 1 ∧
    Z⁻¹ = Complex.sqrt (1 - y) ∧ X⁻¹ = -(I * Complex.sqrt y) ∧
    AnalyticAt ℂ outerRoot y ∧ AnalyticAt ℂ innerRoot y := by
  obtain ⟨ha, hc, h₀, hc₀⟩ := source_roots him
  have hi := mul_ne_zero Complex.I_ne_zero h₀
  have hX := neg_ne_zero.mpr (inv_ne_zero hi)
  have hZ := inv_ne_zero hc₀
  exact ⟨hX, hZ, div_self (mul_ne_zero hX hZ), inv_inv _, by simp [outerRoot],
    ((analyticAt_const.mul ha).inv hi).neg, hc.inv hc₀⟩

private theorem exterior_roots {y : ℂ} (him : 0 < y.im) (hnorm : 1 < ‖y‖) :
    let X := outerRoot y
    let Z := innerRoot y
    ‖X * Z‖ < ‖Z‖ ∧ X = Z * (1 + ((X * Z) / Z) ^ 2) ^ ((2 : ℂ)⁻¹) := by
  let xH := Complex.sqrt (1 - y)
  let zH := I * Complex.sqrt y
  let X := outerRoot y
  let Z := innerRoot y
  obtain ⟨hX, hZ, _, _, _, _, _⟩ := reversal_roots him
  change X ≠ 0 at hX
  change Z ≠ 0 at hZ
  have hy₀ : y ≠ 0 := fun h => by simp [h] at him
  have hcyim : (1 - y).im < 0 := by simpa using neg_neg_of_pos him
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
  have hzre : 0 < (-zH).re := by simpa only [zH, Complex.neg_re, Complex.I_mul_re, neg_neg] using hyim
  have hzim : (-zH).im ≤ 0 := by
    simpa only [zH, Complex.neg_im, Complex.I_mul_im] using neg_nonpos.mpr hyre.le
  have hz₀ : zH ≠ 0 := fun h => by simp [h] at hzre
  have hzSq : zH ^ (2 : ℕ) = -y := by
    rw [show zH = I * Complex.sqrt y from rfl, mul_pow, Complex.I_sq, sqrt_square, neg_one_mul]
  have hrad : 1 < ‖zH‖ := by
    apply (sq_lt_sq₀ zero_le_one (norm_nonneg zH)).mp
    simpa only [one_pow, ← norm_pow, hzSq, norm_neg] using hnorm
  have hXrad : ‖X‖ < 1 := by
    simpa only [X, outerRoot, norm_neg, norm_inv, inv_one] using
      (inv_lt_inv₀ (norm_pos_iff.mpr hz₀) zero_lt_one).mpr hrad
  have hratio : X / Z = xH / (-zH) := by
    simp only [X, Z, outerRoot, innerRoot, xH, zH, div_eq_mul_inv, inv_inv, inv_neg, mul_comm]
  have hrre : 0 < (X / Z).re := by
    have hden : 0 < Complex.normSq (-zH) := Complex.normSq_pos.mpr (neg_ne_zero.mpr hz₀)
    rw [hratio, div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    exact sub_pos.mpr (lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg hxim (div_nonneg (neg_nonneg.mpr hzim) hden.le))
      (mul_pos hxre (div_pos hzre hden)))
  have hratioSq : (X / Z) ^ (2 : ℕ) = 1 - y⁻¹ := by
    rw [hratio, div_pow, neg_sq, show xH ^ (2 : ℕ) = 1 - y from sqrt_square _, hzSq]
    field_simp [hy₀]
    ring
  have hXSq : X ^ (2 : ℕ) = -y⁻¹ := by
    rw [show X = -zH⁻¹ from rfl, neg_sq, inv_pow, hzSq, inv_neg]
  have hRel : (1 + ((X * Z) / Z) ^ (2 : ℕ)) = (X / Z) ^ (2 : ℕ) := by
    rw [mul_div_cancel_right₀ X hZ, hXSq, hratioSq, sub_eq_add_neg]
  refine ⟨?_, ?_⟩
  · simpa only [norm_mul, one_mul] using mul_lt_mul_of_pos_right hXrad (norm_pos_iff.mpr hZ)
  · rw [hRel, Complex.sq_cpow_two_inv hrre, mul_comm]
    exact (div_mul_cancel₀ X hZ).symm

private theorem root_norm_order {y : ℂ} (him : 0 < y.im) :
    (y.re < (1 / 2 : ℝ) → ‖innerRoot y‖ < ‖outerRoot y‖) ∧
    ((1 / 2 : ℝ) < y.re → ‖outerRoot y‖ < ‖innerRoot y‖) := by
  obtain ⟨_, _, h₀, hc₀⟩ := source_roots him
  have hnorm (z : ℂ) : ‖Complex.sqrt z‖ ^ (2 : ℕ) = ‖z‖ := by rw [← norm_pow, sqrt_square]
  have hsum : ‖I * Complex.sqrt y‖ ^ (2 : ℕ) = ‖y‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using hnorm y
  have hpos := norm_pos_iff.mpr (mul_ne_zero Complex.I_ne_zero h₀)
  have hcpos := norm_pos_iff.mpr hc₀
  simp only [outerRoot, innerRoot, norm_neg, norm_inv]
  constructor
  · intro hy
    apply (inv_lt_inv₀ hcpos hpos).mpr
    apply (sq_lt_sq₀ hpos.le hcpos.le).mp
    have h : (1 / 2 : ℝ) < (1 - y).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    simpa only [hsum, hnorm, sub_sub_cancel] using (norm_one_sub_lt_iff (1 - y)).mpr h
  · intro hy
    apply (inv_lt_inv₀ hpos hcpos).mpr
    apply (sq_lt_sq₀ hcpos.le hpos.le).mp
    simpa only [hsum, hnorm] using (norm_one_sub_lt_iff y).mpr hy

private def weight (M K : ℕ) (y : ℂ) (i j : ℕ) : ℂ :=
  ((i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹) *
    (outerRoot y ^ (2 * (i : ℤ) - 6 - 2 * (M : ℤ)) *
      innerRoot y ^ (2 * (j : ℤ) - 6 - 2 * (K : ℤ)))

/-- The raw BHBH amplitude on the chosen reciprocal sheet. The inverse roots
send the HBHB inner root to its negative, contributing the common minus sign. -/
def bhbhUpperAmplitude (M K : ℕ) (P R : TwistedOdd) (Q S : TwistedEven) (y : ℂ) : ℂ :=
  -(I ^ ((M : ℤ) - K) * ∑ i ∈ Finset.range (M / 2 + 1),
    ∑ j ∈ Finset.range (K / 2 + 1), weight M K y i j *
      hbhbUpperAmplitude ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R y)

theorem bhbhUpperAmplitude_analytic (M K : ℕ) (P R : TwistedOdd) (Q S : TwistedEven) :
    AnalyticOnNhd ℂ (bhbhUpperAmplitude M K P R Q S) upperHalfPlane := by
  intro y hy
  obtain ⟨hX, hZ, _, _, _, haX, haZ⟩ := reversal_roots hy
  apply AnalyticAt.neg (analyticAt_const.mul ?_)
  refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => ?_
  refine AnalyticAt.mul ?_ ((hbhbUpperAmplitude_spec ((L₁ false ^ j) Q) S
    ((L₁ true ^ i) P) R).1 y hy)
  exact analyticAt_const.mul ((haX.zpow hX).mul (haZ.zpow hZ))

/-- The same holomorphic function sums the literal A and B double series on
their full upper exterior and upper left native domains, respectively. -/
theorem bhbhUpperAmplitude_hasSum_ab (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    let X := outerRoot y
    let Z := innerRoot y
    (1 < ‖y‖ → HasSum (aJointTerm true P Q R.val S.val (X * Z) Z)
      (bhbhUpperAmplitude M K P R Q S y)) ∧
    (y.re < (1 / 2 : ℝ) → HasSum (bJointTerm false true Q R P S X Z)
      (bhbhUpperAmplitude M K P R Q S y)) := by
  let X := outerRoot y
  let Z := innerRoot y
  let zH := I * Complex.sqrt y
  let xH := Complex.sqrt (1 - y)
  obtain ⟨hX, hZ, hsep, hx', hz', _, _⟩ := reversal_roots hy
  have hswapOdd (w : TwistedOdd) : swapInput (s := true) w = w := Subtype.ext rfl
  have hswapEven (v : TwistedEven) : swapInput (s := false) v = v := Subtype.ext rfl
  constructor
  · intro hE
    obtain ⟨hrad, hLift⟩ := exterior_roots hy hE
    have ha := a_joint_iterate_hasSum_detector_reversal true true M K H J P Q R S
      hP hQ hR hS (d := X * Z) (x := X) (z := Z) (mul_ne_zero hX hZ) hrad hLift
    change (X * Z) / (X * Z) = 1 at hsep
    change X⁻¹ = -zH at hz'
    rw [hsep, hz'] at ha
    simp only [hswapOdd] at ha
    refine Eq.mp (congrArg (HasSum (aJointTerm true P Q R.val S.val (X * Z) Z)) ?_) ha
    simp only [bhbhUpperAmplitude, weight, X, Z, ← mul_neg, ← Finset.sum_neg_distrib]
    apply congrArg (fun z : ℂ => I ^ ((M : ℤ) - K) * z)
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hPi := lowered_grade (s := true) (u := P) hP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have hQj := lowered_grade (s := false) (u := Q) hQ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    change weight M K y i j *
      (∑' p, aJointTerm false ((L₁ false ^ j) Q) ((L₁ true ^ i) P) S.val R.val 1 (-zH) p) =
      weight M K y i j * -(hbhbUpperAmplitude ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R y)
    rw [hbhb_a_tsum_neg_root (K - 2 * j) (M - 2 * i) J H _ _ _ _
      hQj hPi hS hR,
      ((hbhbUpperAmplitude_spec ((L₁ false ^ j) Q) S
        ((L₁ true ^ i) P) R).2.1 y hy hE).tsum_eq]
  · intro hL
    have hb := b_joint_product_hasSum_detector_reversal false true M K H J Q R P S
      hQ hR hP hS (xR := X) (zR := Z) hX hZ ((root_norm_order hy).1 hL)
    change Z⁻¹ = xH at hx'
    change X⁻¹ = -zH at hz'
    rw [hx', hz'] at hb
    refine Eq.mp (congrArg (HasSum (bJointTerm false true Q R P S X Z)) ?_) hb
    simp only [bhbhUpperAmplitude, weight, X, Z, ← mul_neg, ← Finset.sum_neg_distrib]
    apply congrArg (fun z : ℂ => I ^ ((M : ℤ) - K) * z)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hSum := (hbhbUpperAmplitude_spec ((L₁ false ^ j) Q) S ((L₁ true ^ i) P) R).2.2
      y (show y ∈ upperTransportDomain from ⟨hy, hL⟩)
    rw [hswapEven] at hSum
    rw [b_joint_product_neg_root, hSum.tsum_eq, mul_neg]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHBHCanonicalContinuation
