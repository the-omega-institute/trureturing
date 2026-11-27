/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeHBBHDetectorReversal
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Leech HBBH crossing on the reciprocal of the upper BHHB overlap. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedProductRadialInversion
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalIterateInversion

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Finset VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBBHDetectorReversal

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockGradedTrace (actualGrade oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit paritySign)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeFixedUpperRightSkew (rightField)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeMixedPairSkew (swapInput)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedPhysicalIterateInversion (a_joint_iterate_hasSum_detector_reversal)
open NativeFixedProductRadialInversion
  (fixedBJointTerm fixedProductReversalWeight fixed_b_joint_hasSum_detector_reversal)
open NativeBHHBArbitrarySewing (bhhb_actual_complex_sewing_of_states)

open private sqrt_re_positive sqrt_im_positive from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBUpperCrossing
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private aModeLinear aModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial
open private BasisIndex ambientBasis basis_mem_grade coeffAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private BasisQuad component project_basis_val from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit

/-- The upper BHHB coordinate domain parametrizing the reciprocal HBBH overlap. -/
def hbbhOverlap : Set ℂ := {y | 0 < y.im ∧ (1 / 2 : ℝ) < y.re ∧ 1 < ‖1 - y‖}

theorem isOpen_hbbhOverlap : IsOpen hbbhOverlap :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm))

/-- The explicit HBBH roots satisfy both radial bounds and select the
principal relative lift. Reversal gives BHHB outer, inner and separation
roots `I * sqrt y`, `-sqrt (1-y)` and `I`. -/
theorem hbbh_reciprocal_roots {y : ℂ} (hy : y ∈ hbbhOverlap) :
    let X := -(Complex.sqrt (1 - y))⁻¹
    let Z := (I * Complex.sqrt y)⁻¹
    let D := -(Complex.sqrt (1 - y) * Complex.sqrt y)⁻¹
    1 < ‖y‖ ∧ X ≠ 0 ∧ Z ≠ 0 ∧ D ≠ 0 ∧ ‖D‖ < ‖Z‖ ∧ ‖Z‖ < ‖X‖ ∧
      X ^ (2 : ℕ) = (1 - y)⁻¹ ∧ Z ^ (2 : ℕ) = -y⁻¹ ∧
      D ^ (2 : ℕ) = X ^ (2 : ℕ) - Z ^ (2 : ℕ) ∧
      0 < (X / Z).re ∧ X / Z = Complex.sqrt (1 - (1 - y)⁻¹) ∧
      X = Z * (1 + (D / Z) ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹) ∧
      D / (X * Z) = I ∧ Z⁻¹ = I * Complex.sqrt y ∧ X⁻¹ = -Complex.sqrt (1 - y) := by
  obtain ⟨him, hre, hcomp⟩ := hy
  let xH := -Complex.sqrt (1 - y)
  let zH := I * Complex.sqrt y
  let X := -(Complex.sqrt (1 - y))⁻¹
  let Z := zH⁻¹
  let D := -(Complex.sqrt (1 - y) * Complex.sqrt y)⁻¹
  have hcyim : (1 - y).im < 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_lt_zero] using him
  have hxre : xH.re < 0 := by
    simpa only [xH, Complex.neg_re, neg_lt_zero] using sqrt_re_positive (ne_of_lt hcyim)
  have hxim : 0 ≤ xH.im := by
    change 0 ≤ (-Complex.sqrt (1 - y)).im
    rw [Complex.neg_im, Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt hcyim, neg_neg]
    exact Real.sqrt_nonneg _
  have hzre : zH.re < 0 := by
    simpa only [zH, Complex.I_mul_re, neg_lt_zero] using sqrt_im_positive him
  have hzim : 0 < zH.im := by
    simpa only [zH, Complex.I_mul_im] using sqrt_re_positive (ne_of_gt him)
  have hx₀ : xH ≠ 0 := by
    intro h
    simp [h] at hxre
  have hz₀ : zH ≠ 0 := by
    intro h
    simp [h] at hzre
  have hXinv : X⁻¹ = xH := by simp only [X, xH, inv_neg, inv_inv]
  have hZinv : Z⁻¹ = zH := inv_inv _
  have hX : X ≠ 0 := fun h => hx₀ (by simpa only [h, inv_zero] using hXinv.symm)
  have hZ : Z ≠ 0 := inv_ne_zero hz₀
  have hxSq : xH ^ (2 : ℕ) = 1 - y := by rw [show xH = -_ from rfl, neg_sq, sqrt_square]
  have hzSq : zH ^ (2 : ℕ) = -y := by
    rw [show zH = I * Complex.sqrt y from rfl, mul_pow, Complex.I_sq, sqrt_square, neg_one_mul]
  have hXeq : X = xH⁻¹ := by simp only [X, xH, inv_neg]
  have hXSq : X ^ (2 : ℕ) = (1 - y)⁻¹ := by rw [hXeq, inv_pow, hxSq]
  have hZSq : Z ^ (2 : ℕ) = -y⁻¹ := by rw [show Z = zH⁻¹ from rfl, inv_pow, hzSq, inv_neg]
  have hDmul : D = I * (X * Z) := by
    simp only [D, X, Z, zH, mul_inv_rev, Complex.inv_I]
    linear_combination -(Complex.sqrt (1 - y))⁻¹ * (Complex.sqrt y)⁻¹ * Complex.I_sq
  have hD : D ≠ 0 := hDmul ▸ mul_ne_zero Complex.I_ne_zero (mul_ne_zero hX hZ)
  have hnormDiff := (norm_one_sub_lt_iff y).mpr hre
  have hnorm := hcomp.trans hnormDiff
  have hkx : ‖xH‖ ^ (2 : ℕ) = ‖1 - y‖ := by rw [← norm_pow, hxSq]
  have hkz : ‖zH‖ ^ (2 : ℕ) = ‖y‖ := by rw [← norm_pow, hzSq, norm_neg]
  have hrad₁ : 1 < ‖xH‖ := by
    apply (sq_lt_sq₀ zero_le_one (norm_nonneg xH)).mp
    simpa only [one_pow, hkx] using hcomp
  have hrad₂ : ‖xH‖ < ‖zH‖ := by
    apply (sq_lt_sq₀ (norm_nonneg xH) (norm_nonneg zH)).mp
    simpa only [hkx, hkz] using hnormDiff
  have hXrad : ‖X‖ < 1 := by
    rw [hXeq, norm_inv, ← inv_one (G := ℝ)]
    exact (inv_lt_inv₀ (norm_pos_iff.mpr hx₀) zero_lt_one).mpr hrad₁
  have hArad : ‖D‖ < ‖Z‖ := by
    rw [hDmul, norm_mul, Complex.norm_I, one_mul, norm_mul]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hZ) hXrad
  have hBrad : ‖Z‖ < ‖X‖ := by
    rw [show Z = zH⁻¹ from rfl, hXeq, norm_inv, norm_inv]
    exact (inv_lt_inv₀ (norm_pos_iff.mpr hz₀) (norm_pos_iff.mpr hx₀)).mpr hrad₂
  have hratio : X / Z = zH / xH := by
    simp only [hXeq, Z, div_eq_mul_inv, inv_inv, mul_comm]
  have hrre : 0 < (X / Z).re := by
    have hden := Complex.normSq_pos.mpr hx₀
    rw [hratio, div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    exact sub_pos.mpr ((mul_nonpos_of_nonneg_of_nonpos hzim.le
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hxim) hden.le)).trans_lt
      (mul_pos_of_neg_of_neg hzre (div_neg_of_neg_of_pos hxre hden)))
  have hy₁ : 1 - y ≠ 0 := by
    intro h
    simp [h] at hcyim
  have hy₀ : y ≠ 0 := by
    intro h
    simp [h] at him
  have hratioSq : (X / Z) ^ (2 : ℕ) = 1 - (1 - y)⁻¹ := by
    rw [hratio, div_pow, hxSq, hzSq]
    field_simp [hy₁]
    ring
  have hprincipal : X / Z = Complex.sqrt (1 - (1 - y)⁻¹) := by
    rw [Complex.sqrt, ← hratioSq, Complex.sq_cpow_two_inv hrre]
  have hDZ : D / Z = I * X := by rw [hDmul, ← mul_assoc, mul_div_cancel_right₀ _ hZ]
  have hRel : 1 + (D / Z) ^ (2 : ℕ) = (X / Z) ^ (2 : ℕ) := by
    simp only [hDZ, mul_pow, Complex.I_sq, hXSq, hratioSq, neg_one_mul, sub_eq_add_neg]
  have hLift : X = Z * (1 + (D / Z) ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹) := by
    rw [hRel, Complex.sq_cpow_two_inv hrre, mul_comm, div_mul_cancel₀ _ hZ]
  have hDSq : D ^ (2 : ℕ) = X ^ (2 : ℕ) - Z ^ (2 : ℕ) := by
    rw [hDmul, mul_pow, Complex.I_sq, mul_pow, hXSq, hZSq]
    field_simp [hy₀, hy₁]
    ring
  have hDinv : D / (X * Z) = I := by rw [hDmul, mul_div_cancel_right₀ _ (mul_ne_zero hX hZ)]
  exact ⟨hnorm, hX, hZ, hD, hArad, hBrad, hXSq, hZSq, hDSq,
    hrre, hprincipal, hLift, hDinv, hZinv, hXinv⟩

set_option maxHeartbeats 4000000 in
/-- In HBBH order `(P,Q,R,S)`, the native mixed A iterate and fixed B
product have opposite double-mode sums throughout the reciprocal overlap. -/
theorem hbbh_actual_complex_sewing_of_homogeneous (M K L N : ℕ)
    (P S : TwistedEven) (Q R : TwistedOdd)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {y : ℂ} (hy : y ∈ hbbhOverlap) :
    let X := -(Complex.sqrt (1 - y))⁻¹
    let Z := (I * Complex.sqrt y)⁻¹
    let D := -(Complex.sqrt (1 - y) * Complex.sqrt y)⁻¹
    let A := aJointTerm false P Q R.val S.val D Z
    let B := fixedBJointTerm true false Q R P S X Z
    HasSum A (∑' p, A p) ∧ HasSum B (-(∑' p, A p)) := by
  let xH := -Complex.sqrt (1 - y)
  let zH := I * Complex.sqrt y
  let X := -(Complex.sqrt (1 - y))⁻¹
  let Z := zH⁻¹
  let D := -(Complex.sqrt (1 - y) * Complex.sqrt y)⁻¹
  obtain ⟨hnorm, hX, hZ, hD, hradA, hradB, _, _, _, _, _, hLift, hsep, hZinv, hXinv⟩ :=
    hbbh_reciprocal_roots hy
  change D / (X * Z) = I at hsep
  change Z⁻¹ = zH at hZinv
  change X⁻¹ = xH at hXinv
  have ha := a_joint_iterate_hasSum_detector_reversal false true M K L N P Q R S
    hP hQ hR hS (d := D) (x := X) (z := Z) hD hradA hLift
  have hb := fixed_b_joint_hasSum_detector_reversal true false M K L N Q R P S
    hQ hR hP hS (xR := X) (zR := Z) hX hZ hradB
  rw [hsep, hXinv] at ha
  rw [hZinv, hXinv] at hb
  have hswapEven (v : TwistedEven) : swapInput (s := false) v = v := Subtype.ext rfl
  have hswapOdd (w : TwistedOdd) : swapInput (s := true) w = w := Subtype.ext rfl
  simp only [hswapEven, hswapOdd, fixedProductReversalWeight] at ha hb
  let A := aJointTerm false P Q R.val S.val D Z
  let B := fixedBJointTerm true false Q R P S X Z
  let aDesc (i j : ℕ) :=
    aJointTerm true ((L₁ true ^ j) Q) ((L₁ false ^ i) P) S.val R.val I xH
  let bDesc (i j : ℕ) :=
    fixedBJointTerm false true ((L₁ false ^ i) P) S ((L₁ true ^ j) Q) R zH xH
  have hdesc (i j : ℕ) : (∑' p, bDesc i j p) = -(∑' p, aDesc i j p) :=
    (bhhb_actual_complex_sewing_of_states ((L₁ true ^ j) Q) ((L₁ false ^ i) P)
      S R hy.1 hy.2.1 hnorm hy.2.2).2.tsum_eq
  let V : ℂ := I ^ ((M : ℤ) - K) * ∑ i ∈ Finset.range (M / 2 + 1),
    ∑ j ∈ Finset.range (K / 2 + 1),
      fixedProductReversalWeight M K X Z i j * ∑' p, aDesc i j p
  have hA : HasSum A V := ha
  have hB : HasSum B (-V) := by
    change HasSum B (I ^ ((M : ℤ) - K) * ∑ i ∈ Finset.range (M / 2 + 1),
      ∑ j ∈ Finset.range (K / 2 + 1),
        fixedProductReversalWeight M K X Z i j * ∑' p, bDesc i j p) at hb
    simpa only [hdesc, mul_neg, Finset.sum_neg_distrib, V] using hb
  change HasSum A (∑' p, A p) ∧ HasSum B (-(∑' p, A p))
  rw [hA.tsum_eq]
  exact ⟨hA, hB⟩


private abbrev HBBHLinear :=
  TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ

private def aMode (D Z : ℂ) (p : ℤ × ℤ) : HBBHLinear :=
  aModeLinear false true D Z p

private theorem aMode_apply (D Z : ℂ) (p : ℤ × ℤ)
    (P S : TwistedEven) (Q R : TwistedOdd) :
    aMode D Z p P Q R S = aJointTerm false P Q R.val S.val D Z p :=
  aModeLinear_apply false true D Z p P Q R S

private def bMode (X Z : ℂ) (p : ℤ × ℤ) : HBBHLinear :=
  let inner := (coeffAt p.1).comp (nu true)
  let outer := ((coeffAt p.2).comp (rightField ℒ leechUnit false)).flip
  let sub := (paritySpace ℒ leechUnit (paritySign false)).subtype
  let pair := ((actualForm ℒ leechUnit).flip.compl₂ sub).comp sub
  let moveOuter : (TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  (Z ^ p.1 * X ^ p.2) • (moveOuter.comp (inner.compr₂ (outer.compr₂ pair))).flip

private theorem bMode_apply (X Z : ℂ) (p : ℤ × ℤ)
    (P S : TwistedEven) (Q R : TwistedOdd) :
    bMode X Z p P Q R S = fixedBJointTerm true false Q R P S X Z p :=
  mul_comm _ _

private theorem component_grade (s : Bool) (u : Twisted ℒ leechUnit s) (i : BasisIndex) :
    (component s u i).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  change (ambientBasis.repr u.val i • project s (ambientBasis i)).val ∈ _
  rw [Submodule.coe_smul, project_basis_val]
  apply Submodule.smul_mem
  split_ifs <;> first | exact basis_mem_grade i | exact Submodule.zero_mem _

private def basisTuples (P S : TwistedEven) (Q R : TwistedOdd) : Finset BasisQuad :=
  (ambientBasis.repr P.val).support ×ˢ ((ambientBasis.repr Q.val).support ×ˢ
    ((ambientBasis.repr R.val).support ×ˢ (ambientBasis.repr S.val).support))

private abbrev onComponents (P S : TwistedEven) (Q R : TwistedOdd)
    (F : HBBHLinear) (i : BasisQuad) : ℂ :=
  F (component false P i.1) (component true Q i.2.1)
    (component true R i.2.2.1) (component false S i.2.2.2)

private theorem expand (P S : TwistedEven) (Q R : TwistedOdd) (F : HBBHLinear) :
    F P Q R S = ∑ i ∈ basisTuples P S Q R, onComponents P S Q R F i := by
  classical
  conv_lhs =>
    rw [← sum_projectedBasis false P]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis true Q]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis true R]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis false S]
    simp only [map_sum]
  simp only [basisTuples, Finset.sum_product]

set_option maxHeartbeats 4000000 in
/-- Finite expansion in the projected homogeneous basis gives the same
opposite native HBBH sums for arbitrary actual twisted states. -/
theorem hbbh_actual_complex_sewing_of_states
    (P S : TwistedEven) (Q R : TwistedOdd) {y : ℂ} (hy : y ∈ hbbhOverlap) :
    let X := -(Complex.sqrt (1 - y))⁻¹
    let Z := (I * Complex.sqrt y)⁻¹
    let D := -(Complex.sqrt (1 - y) * Complex.sqrt y)⁻¹
    let A := aJointTerm false P Q R.val S.val D Z
    let B := fixedBJointTerm true false Q R P S X Z
    HasSum A (∑' p, A p) ∧ HasSum B (-(∑' p, A p)) := by
  classical
  let X := -(Complex.sqrt (1 - y))⁻¹
  let Z := (I * Complex.sqrt y)⁻¹
  let D := -(Complex.sqrt (1 - y) * Complex.sqrt y)⁻¹
  let A := aMode D Z
  let B := bMode X Z
  let value (i : BasisQuad) := ∑' p, onComponents P S Q R (A p) i
  have hcomponent (i : BasisQuad) :
      HasSum (fun p => onComponents P S Q R (A p) i) (value i) ∧
      HasSum (fun p => onComponents P S Q R (B p) i) (-value i) := by
    have h := hbbh_actual_complex_sewing_of_homogeneous
      (oddWeight ℒ i.1.1) (oddWeight ℒ i.2.1.1)
      (oddWeight ℒ i.2.2.1.1) (oddWeight ℒ i.2.2.2.1)
      (component false P i.1) (component false S i.2.2.2)
      (component true Q i.2.1) (component true R i.2.2.1)
      (component_grade false P i.1) (component_grade true Q i.2.1)
      (component_grade true R i.2.2.1) (component_grade false S i.2.2.2) hy
    simpa only [value, onComponents, A, B, aMode_apply, bMode_apply, X, Z, D] using h
  let V := ∑ i ∈ basisTuples P S Q R, value i
  have hA : HasSum (fun p => A p P Q R S) V :=
    (hasSum_sum (s := basisTuples P S Q R) fun i _ => (hcomponent i).1).congr_fun
      (fun p => expand P S Q R (A p))
  have hB : HasSum (fun p => B p P Q R S) (-V) := by
    have hnegV : -V = ∑ i ∈ basisTuples P S Q R, -value i := by
      simp only [V, Finset.sum_neg_distrib]
    rw [hnegV]
    exact (hasSum_sum (s := basisTuples P S Q R) fun i _ => (hcomponent i).2).congr_fun
      (fun p => expand P S Q R (B p))
  have hBoth : HasSum (fun p => A p P Q R S) (∑' p, A p P Q R S) ∧
      HasSum (fun p => B p P Q R S) (-(∑' p, A p P Q R S)) := by
    rw [hA.tsum_eq]
    exact ⟨hA, hB⟩
  simpa only [A, B, aMode_apply, bMode_apply, X, Z, D] using hBoth

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBBHDetectorReversal
