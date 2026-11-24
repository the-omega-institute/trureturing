/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeHBHBUpperAD
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native marked HBHB A/D crossing on the upper right exterior. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperCrossing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate

/-! The marked HBHB A/D bridge on the upper right exterior. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct Topology VertexOperator
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeOddUpperRightSkew (lowering)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation sigma)
open NativeFixedPairAIterate (fixedASlitSewn fixedAIterate_hasSum)
open NativeFixedCrossedProductToIterate (dJointTerm translatedDetector translationWeight
  hhbb_upper_fixed_d_joint_hasSum)
open NativeMixedComplexSewing (hhbb_actual_complex_sewing)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator)
open NativeMixedUpperDLip (dSlitProduct)
open NativeHHBBUpperDAnalyticAgreement (upperCap isOpen_upperCap)
open NativeHHBBUpperHalfPlaneBD
  (hhbb_marked_rawD_eq_neg_rawB_upper_half_plane hhbb_marked_rawD_hasSum_upper_exterior)
open NativeMixedAIterateRadial (aJointTerm mixed_a_joint_summable_of_homogeneous)
open NativeMixedCrossedProductToIterate (mixed_d_joint_hasSum_crossed_a)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (ball_subset_slitDomain isOpen_slitDomain slitDomain)

open private sqrt_square square_root_disk zpow_double a_joint_from_diagonal from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff ratio_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private fixedASlitSewn_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairAIterate
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit true

private theorem marked_grade {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (i : Puncture) (g : ActualGround ℒ leechUnit) :
    wordAt ℒ slot colour n l i ⊗ₜ[ℂ] g ∈
      actualGrade ℒ leechUnit (doubledOccupation slot n l i).toNat := by
  rw [occupationGrade_eq slot colour n l i]
  exact wordAt_grade slot colour n l i g

private theorem right_ratio {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re) :
    y ≠ 0 ∧ 1 - y ≠ 0 ∧ ‖(1 - y) / y‖ < 1 := by
  have hy₀ : y ≠ 0 := by
    rintro rfl
    simp at him
  have hy₁ : 1 - y ≠ 0 := by
    intro h
    have heq : y = 1 := (sub_eq_zero.mp h).symm
    simp [heq] at him
  refine ⟨hy₀, hy₁, ?_⟩
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hy₀)]
  exact (norm_one_sub_lt_iff y).mpr hre

private theorem fixed_value_analytic (numerator : ℂ → ℂ) (s a : ℤ)
    (hnum : DifferentiableOn ℂ numerator slitDomain)
    {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re) :
    AnalyticAt ℂ (fun z =>
      z ^ (-s) * (((1 - z) / z) ^ (-a) * numerator (-((1 - z) / z)))) y := by
  obtain ⟨hy₀, hy₁, ht₁⟩ := right_ratio him hre
  have ht₀ := div_ne_zero hy₁ hy₀
  have ht := ratio_analytic hy₀
  have hneg : -((1 - y) / y) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg]
    exact ht₁
  have ha := hnum.analyticOnNhd isOpen_slitDomain (-((1 - y) / y))
    (ball_subset_slitDomain hneg)
  have hc := AnalyticAt.comp (f := fun z : ℂ => -((1 - z) / z)) (g := numerator) ha ht.neg
  exact ((analyticAt_id (z := y)).zpow (n := -s) hy₀).mul ((ht.zpow (n := -a) ht₀).mul hc)

private theorem aJointTerm_translated_detector (s : Bool)
    (u : Twisted ℒ leechUnit s) (w : Twisted ℒ leechUnit (!s)) (v : TwistedEven) (b : TwistedOdd)
    (N : ℕ) (y dR zR : ℂ) (i : ℤ × ℤ) :
    aJointTerm s u w v.val (translatedDetector true N y b).val dR zR i =
      ∑ j ∈ Finset.range (N / 2 + 1), (y ^ j / (j.factorial : ℂ)) *
        aJointTerm s u w v.val ((L₁ ^ j) b).val dR zR i := by
  let c := (correctedField ℒ leechUnit ((mu s u).coeff i.1 w).val).coeff i.2 v.val
  let f := (actualForm ℒ leechUnit).flip c
  change f (translatedDetector true N y b).val * (dR ^ i.1 * zR ^ i.2) = _
  simp only [translatedDetector, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change (translationWeight y j * f ((L₁ ^ j) b).val) * _ =
    (y ^ j / (j.factorial : ℂ)) * (f ((L₁ ^ j) b).val * _)
  rw [translationWeight, div_eq_mul_inv, mul_assoc]

set_option maxHeartbeats 4000000 in
-- Combines the native crossed product and all its finite detector summands.
/-- On the upper exterior, the marked transported HBHB A sum has value `-B₀ y`.
The detector is the finite action of `exp(y L(1))` on the original grade-`N`
detector. The source HHBB D has the same value at roots `sqrt y` and `1`. -/
theorem hbhb_marked_a_hasSum_upper_exterior {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℂ} (him : 0 < y.im) (hy : 1 < ‖y‖) :
    let H (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    let B₀ := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
    HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1), (y ^ j / (j.factorial : ℂ)) *
      aJointTerm false u w v.val ((L₁ ^ j) b).val 1 (I * Complex.sqrt y) i) (-B₀) ∧
      HasSum (aJointTerm false u w v.val (translatedDetector true N y b).val
        1 (I * Complex.sqrt y)) (-B₀) := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let B₀ := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
    I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
  let D₀ := y ^ (-sigma (M : ℤ) K L N) *
    dSlitProduct M K L N (V .P) (V .Q) (V .R) (V .S) p q r d y⁻¹
  let T (j : ℕ) := (L₁ ^ j) b
  let term (j : ℕ) := aJointTerm false u w v.val (T j).val 1 (I * Complex.sqrt y)
  let A := ∑ j ∈ Finset.range (N / 2 + 1),
    (y ^ j / (j.factorial : ℂ)) * (∑' i : ℤ × ℤ, term j i)
  change HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
      (y ^ j / (j.factorial : ℂ)) * term j i) (-B₀) ∧
    HasSum (aJointTerm false u w v.val (translatedDetector true N y b).val
      1 (I * Complex.sqrt y)) (-B₀)
  have huG : u.val ∈ actualGrade ℒ leechUnit M := hu.symm ▸ marked_grade slot colour n l .P p
  have hvG : v.val ∈ actualGrade ℒ leechUnit K := hv.symm ▸ marked_grade slot colour n l .Q q
  have hwG : w.val ∈ actualGrade ℒ leechUnit L := hw.symm ▸ marked_grade slot colour n l .R r
  have hbG : b.val ∈ actualGrade ℒ leechUnit N := hb.symm ▸ marked_grade slot colour n l .S d
  have hRootSq : ‖Complex.sqrt y‖ ^ (2 : ℕ) = ‖y‖ := by rw [← norm_pow, sqrt_square]
  have hRad : ‖(1 : ℂ)‖ < ‖Complex.sqrt y‖ := by
    rw [norm_one]
    apply (sq_lt_sq₀ (zero_le_one : (0 : ℝ) ≤ 1) (norm_nonneg (Complex.sqrt y))).mp
    rwa [one_pow, hRootSq]
  have hRoot : Complex.sqrt y ≠ 0 :=
    norm_pos_iff.mp ((by simp : 0 < ‖(1 : ℂ)‖).trans hRad)
  have hRaw := (hhbb_marked_rawD_hasSum_upper_exterior slot colour n l hpar
    u v w b p q r d hu hv hw hb him hy).1
  change HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1) D₀ at hRaw
  have hRawEq : D₀ = -B₀ :=
    (hhbb_marked_rawD_eq_neg_rawB_upper_half_plane slot colour n l hl hpar
      u v w b p q r d hu hv hw hb).2.2 him
  have hCross := mixed_d_joint_hasSum_crossed_a false false M L K N u w v b
    huG hwG hvG hbG one_ne_zero hRoot hRad
  simp only [pow_mul, sqrt_square] at hCross
  change HasSum (bJointTerm false false u w v b (Complex.sqrt y) 1) A at hCross
  have hAValue : A = -B₀ := (hCross.unique hRaw).trans hRawEq
  have hRadA : ‖(1 : ℂ)‖ < ‖I * Complex.sqrt y‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using hRad
  have hSums (j : ℕ) (hj : j ∈ Finset.range (N / 2 + 1)) : Summable (term j) :=
    mixed_a_joint_summable_of_homogeneous false false M L K (N - 2 * j) u w v (T j)
      huG hwG hvG (lowered_grade (s := true) (u := b) hbG
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) one_ne_zero hRadA
  have hsum : HasSum (fun i => ∑ j ∈ Finset.range (N / 2 + 1),
      (y ^ j / (j.factorial : ℂ)) * term j i) A :=
    hasSum_sum (s := Finset.range (N / 2 + 1)) fun j hj => (hSums j hj).hasSum.mul_left _
  rw [← hAValue]
  exact ⟨hsum, hsum.congr_fun (aJointTerm_translated_detector false u w v b N y 1
    (I * Complex.sqrt y))⟩

set_option maxHeartbeats 4000000 in
-- Elaborates the analytic continuation and the native fixed-pair mode sums.
/-- On the upper half-plane to the right of `Re y = 1/2`, fixed HBHB D
at roots `sqrt (1-y)` and `I * sqrt y` is the original HHBB A iterate
with its transported detector. The HHBB overlap determines its value by
analytic continuation throughout the convex upper right domain. -/
theorem hbhb_marked_d_hasSum_upper_right {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re) :
    let H (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := H .P
    let K := H .Q
    let L := H .R
    let N := H .S
    let B₀ := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y
    HasSum (dJointTerm false true u v w (translatedDetector true N y b)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (-B₀) := by
  let H (i : Puncture) := (doubledOccupation slot n l i).toNat
  let V := wordAt ℒ slot colour n l
  let M := H .P
  let K := H .Q
  let L := H .R
  let N := H .S
  let s := sigma (M : ℤ) K L N
  let a := ((M : ℤ) + K + 6) / 2
  let t (z : ℂ) := (1 - z) / z
  let numerator := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d
  let A₀ (z : ℂ) := z ^ (-s) * (t z ^ (-a) * numerator (-(t z)))
  let B₀ (z : ℂ) := Complex.sqrt z ^ (-(6 + (K : ℤ) + L)) *
    I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d z
  change HasSum (dJointTerm false true u v w (translatedDetector true N y b)
    (Complex.sqrt (1 - y)) (I * Complex.sqrt y)) (-(B₀ y))
  let U : Set ℂ := {z | 0 < z.im} ∩ {z | (1 / 2 : ℝ) < z.re}
  have hU : IsPreconnected U :=
    ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_halfSpace_re_gt (1 / 2 : ℝ))).isPreconnected
  have hA₀ : AnalyticOnNhd ℂ A₀ U := fun z hz =>
    fixed_value_analytic numerator s a
      (fixedASlitSewn_differentiableOn M K (V .P) (V .Q) (V .R) (V .S) p q r d) hz.1 hz.2
  have hB₀ : AnalyticOnNhd ℂ B₀ U :=
    (hhbb_marked_rawD_eq_neg_rawB_upper_half_plane slot colour n l hl hpar
      u v w b p q r d hu hv hw hb).1.mono (fun _ hz => hz.1)
  let y₀ : ℂ := ⟨3 / 4, 1 / 4⟩
  have hy₀re : (1 / 2 : ℝ) < y₀.re := by
    change (1 / 2 : ℝ) < 3 / 4
    norm_num
  have hy₀im : 0 < y₀.im := by
    change (0 : ℝ) < 1 / 4
    norm_num
  have hy₀norm : ‖y₀‖ < 1 := by
    apply (sq_lt_sq₀ (norm_nonneg y₀) (zero_le_one : (0 : ℝ) ≤ 1)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    change (3 / 4 : ℝ) * (3 / 4) + (1 / 4) * (1 / 4) < 1 ^ (2 : ℕ)
    norm_num
  have hy₀cap : y₀ ∈ upperCap := ⟨⟨mem_ball_zero_iff.mpr hy₀norm, hy₀re⟩, hy₀im⟩
  have hgerm : A₀ =ᶠ[𝓝 y₀] -B₀ := by
    filter_upwards [isOpen_upperCap.mem_nhds hy₀cap] with z hz
    exact (hhbb_actual_complex_sewing slot colour n l hl hpar u v w b p q r d hu hv hw hb
      (xRoot := 1) one_ne_zero (mem_ball_zero_iff.mp hz.1.1) hz.1.2
      (sqrt_square (t z))).2.2.2.1
  have hValue : A₀ y = -(B₀ y) :=
    (hA₀.eqOn_of_preconnected_of_eventuallyEq hB₀.neg hU ⟨hy₀im, hy₀re⟩ hgerm) ⟨him, hre⟩
  have hG (i : Puncture) : (H i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l i, punctureExcitation_cast]
  have hM₀ : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
  have hK₀ : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
  have hL₁ : (L : ℤ) % 2 = 1 := by simpa only [L, hG] using hpar.2.2.1
  have hN₁ : (N : ℤ) % 2 = 1 := by simpa only [N, hG] using hpar.2.2.2
  have hM : Even M := (Int.even_coe_nat M).mp (Int.even_iff.mpr hM₀)
  have hK : Even K := (Int.even_coe_nat K).mp (Int.even_iff.mpr hK₀)
  have hMK : Even ((M : ℤ) + K) := Int.even_iff.mpr (by omega)
  have huG : u.val ∈ actualGrade ℒ leechUnit M := hu.symm ▸ marked_grade slot colour n l .P p
  have hvG : v.val ∈ actualGrade ℒ leechUnit K := hv.symm ▸ marked_grade slot colour n l .Q q
  have hRG := marked_grade slot colour n l .R r
  have hSG := marked_grade slot colour n l .S d
  have hwG : w.val ∈ actualGrade ℒ leechUnit L := hw.symm ▸ hRG
  have hbG : b.val ∈ actualGrade ℒ leechUnit N := hb.symm ▸ hSG
  obtain ⟨hy₀, hy₁, ht⟩ := right_ratio him hre
  let zR := Complex.sqrt y
  let dR := Complex.sqrt (1 - y)
  let ξ := dR / zR
  have hzSq : zR ^ (2 : ℕ) = y := sqrt_square y
  have hz₀ : zR ≠ 0 := fun h => hy₀ (by simpa [h] using hzSq.symm)
  have hξSq : ξ ^ (2 : ℕ) = t y := by
    dsimp only [ξ, t, dR, zR]
    rw [div_pow, sqrt_square, sqrt_square]
  obtain ⟨hξ₀, hξ₁⟩ := square_root_disk hξSq (div_ne_zero hy₁ hy₀) ht
  have hsum := fixedAIterate_hasSum false M K L N u v (V .P) (V .Q) (V .R) (V .S) p q r d
    huG hvG hu hv hRG hSG hMK hξ₀ hξ₁
  have hPole : -((M : ℤ) + K + 6) = 2 * (-a) := by
    dsimp only [a]
    omega
  rw [hPole, zpow_double, hξSq] at hsum
  have hsum' : HasSum (fun j : ℤ =>
      NativeFixedPairAIterate.fixedAIterateCoeff false M K L N j u v w.val b.val * ξ ^ j)
      (t y ^ (-a) * numerator (-(t y))) := by
    simpa only [hw, hb, numerator] using hsum
  have hA := a_joint_from_diagonal M K L N u v w b huG hvG hwG hbG hM hK hz₀ hsum'
  have hDegree : (N : ℤ) - L - ((M : ℤ) + K + 6) = 2 * (-s) := by
    dsimp only [s, sigma]
    omega
  have hLift : zR * ξ = dR := mul_div_cancel₀ dR hz₀
  rw [hLift, hDegree, zpow_double, hzSq] at hA
  change HasSum (NativeMixedComplexSewing.aJointTerm u v w b dR zR) (A₀ y) at hA
  rw [hValue] at hA
  have hD := hhbb_upper_fixed_d_joint_hasSum M K L N u v w b (y := y)
    huG hvG hwG hbG (Ne.symm (sub_ne_zero.mp hy₁)) hre
  rw [hA.tsum_eq] at hD
  exact hD

/-- Marked native HBHB A and D sum to the same value throughout the upper
right exterior, with the same translated detector. -/
theorem hbhb_marked_upper_ad {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d)
    {y : ℂ} (him : 0 < y.im) (hy : 1 < ‖y‖) (hre : (1 / 2 : ℝ) < y.re) :
    let N := (doubledOccupation slot n l .S).toNat
    let b' := translatedDetector true N y b
    let A := aJointTerm false u w v.val b'.val 1 (I * Complex.sqrt y)
    let D := dJointTerm false true u v w b' (Complex.sqrt (1 - y)) (I * Complex.sqrt y)
    HasSum A (∑' i, D i) ∧ HasSum D (∑' i, D i) := by
  dsimp only
  have hA := (hbhb_marked_a_hasSum_upper_exterior slot colour n l hl hpar
    u v w b p q r d hu hv hw hb him hy).2
  have hD := hbhb_marked_d_hasSum_upper_right slot colour n l hl hpar
    u v w b p q r d hu hv hw hb him hre
  rw [hD.tsum_eq]
  exact ⟨hA, hD⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD
