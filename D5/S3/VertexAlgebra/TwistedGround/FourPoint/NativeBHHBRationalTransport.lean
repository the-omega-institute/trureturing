/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeBHHBRationalTransport
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native BHHB transport of the normalized HHBB amplitude with finite detector translation. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBTwoVariableRational

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBRationalTransport

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedPairField (nu_coeff_odd_zero)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeFixedCrossedProductToIterate (dJointTerm translationWeight translatedDetector
  fixed_d_joint_hasSum_crossed_a upper_fixed_d_joint_hasSum)
open NativeBHHBUpperCrossing (bJointTerm)
open NativeBHHBArbitrarySewing (bhhb_actual_complex_sewing_of_states)
open NativeHHBBTwoVariableRational (denominator evalAt homogenizedNumerator
  hhbb_marked_two_variable_common_rational)

open private aJointTerm_neg_outer_root from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private fixed_d_neg_pair_root from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBUpperCrossing
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private marked_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHBHBUpperAD

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit true
local notation "hhbbA" => NativeMixedComplexSewing.aJointTerm
local notation "fixedA" => NativeFixedCrossedProductToIterate.aJointTerm
local notation "bhhbA" => NativeMixedAIterateRadial.aJointTerm

private theorem hhbb_aJointTerm_neg_difference (u v : TwistedEven) (w b : TwistedOdd)
    (D Z : ℂ) (i : ℤ × ℤ) :
    hhbbA u v w b (-D) Z i = hhbbA u v w b D Z i := by
  by_cases h : Even i.1
  · simp only [NativeMixedComplexSewing.aJointTerm, h.neg_zpow]
  · simp only [NativeMixedComplexSewing.aJointTerm,
      nu_coeff_odd_zero false i.1 u v (Int.not_even_iff_odd.mp h),
      Submodule.coe_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply, zero_mul]

/-- On the BHHB product chart with roots `I * Z, -D`, a homogeneous
literal detector has a finite expansion in HHBB iterates with roots
`D, Z`. The detector translation is by the BHHB first coordinate `-Z²`. -/
theorem bhhb_b_hasSum_hhbb_a (M K L N : ℕ) (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {D Z : ℂ} (hD : D ≠ 0) (hrad : ‖D‖ < ‖Z‖) :
    HasSum (bJointTerm w u v b (I * Z) (-D))
      (∑ j ∈ Finset.range (N / 2 + 1), translationWeight (-(Z ^ 2)) j *
        ∑' i, hhbbA u v w ((L₁ ^ j) b) D Z i) := by
  have hZ : Z ≠ 0 := norm_pos_iff.mp ((norm_nonneg D).trans_lt hrad)
  have hrad' : ‖-D‖ < ‖I * Z‖ := by simpa only [norm_neg, norm_mul, Complex.norm_I, one_mul]
  have h := fixed_d_joint_hasSum_crossed_a false true M K L N u v w b hu hv hw hb
    (xR := -D) (zR := I * Z) (neg_ne_zero.mpr hD) (mul_ne_zero Complex.I_ne_zero hZ) hrad'
  have hsq : (I * Z) ^ (2 : ℕ) = -(Z ^ 2) := by rw [mul_pow, Complex.I_sq, neg_one_mul]
  have hturn : I * (I * Z) = -Z := by rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  rw [hsq, hturn] at h
  simp only [aJointTerm_neg_outer_root] at h
  have hterm (j : ℕ) (i : ℤ × ℤ) :
      fixedA false true u v w ((L₁ ^ j) b) (-D) Z i =
        hhbbA u v w ((L₁ ^ j) b) D Z i :=
    hhbb_aJointTerm_neg_difference u v w ((L₁ ^ j) b) D Z i
  change HasSum (dJointTerm false true u v w b (-D) (I * Z)) _
  simpa only [hterm] using h

/-- At BHHB coordinates `(-y, 1-y)` the two native normalized sums
are the finite inverse detector translation of the normalized HHBB iterate.
The product has phase `I` and the iterate has phase `-I`. -/
theorem bhhb_hasSum_normalized_hhbb_finite_expansion
    (M K L N : ℕ) (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {y : ℂ} (him : 0 < y.im) (hre : (1 / 2 : ℝ) < y.re)
    (hy : 1 < ‖y‖) (hcomp : 1 < ‖1 - y‖) :
    let D := Complex.sqrt (1 - y)
    let Z := Complex.sqrt y
    let value := ∑ j ∈ Finset.range (N / 2 + 1), ((-y) ^ j / (j.factorial : ℂ)) *
      ∑' i, Z * hhbbA u v w ((L₁ ^ j) b) D Z i
    HasSum (fun i => (I * Z) * bhhbA true w u v.val b.val I (-D) i) (-(I * value)) ∧
    HasSum (fun i => (I * Z) * bJointTerm w u v b (I * Z) (-D) i) (I * value) := by
  intro D Z value
  have hd : D ≠ 0 := by
    intro h
    have hs : D ^ (2 : ℕ) = 1 - y := sqrt_square _
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    rw [← hs, norm_zero] at hcomp
    exact (by norm_num : ¬ (1 : ℝ) < 0) hcomp
  have hrad : ‖D‖ < ‖Z‖ := by
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [← norm_pow, D, Z, sqrt_square] using (norm_one_sub_lt_iff y).mpr hre
  have hB := bhhb_b_hasSum_hhbb_a M K L N u v w b hu hv hw hb hd hrad
  have hS := bhhb_actual_complex_sewing_of_states w u v b him hre hy hcomp
  have hA := hS.1
  rw [← neg_neg (∑' i : ℤ × ℤ, bhhbA true w u v.val b.val I (-D) i),
    hS.2.unique hB] at hA
  have heq : (I * Z) * (∑ j ∈ Finset.range (N / 2 + 1),
      translationWeight (-(Z ^ 2)) j * ∑' i, hhbbA u v w ((L₁ ^ j) b) D Z i) =
      I * value := by
    simp only [value, translationWeight, div_eq_mul_inv, tsum_mul_left, Finset.mul_sum,
      show Z ^ (2 : ℕ) = y from sqrt_square y]
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨?_, ?_⟩
  · simpa only [mul_neg, heq] using hA.mul_left (I * Z)
  · simpa only [heq] using hB.mul_left (I * Z)

set_option maxHeartbeats 4000000 in
/-- The upper transport `(x,z) ↦ (-z,x-z)` lifts to `(I*Z,-D)` in
BHHB. Translating the detector by `z` carries the normalized HHBB rational
value to the BHHB product with phase `I`. In BHHB coordinates `xB,zB`
the original evaluation point is `(zB-xB,-xB)`. -/
theorem bhhb_marked_b_hasSum_hhbb_rational {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let degree : ℕ := (12 + M + K + L + N) / 2
    ∃ P : Polynomial ℂ, P.natDegree ≤ degree ∧
      ∀ X Z D : ℂ, X ≠ 0 →
        let y := Z ^ (2 : ℕ) / X ^ (2 : ℕ)
        0 < y.im → (1 / 2 : ℝ) < y.re →
        Z / X = Complex.sqrt y → D / X = Complex.sqrt (1 - y) →
        let xB := (I * Z) ^ (2 : ℕ)
        let zB := (-D) ^ (2 : ℕ)
        let value := evalAt (zB - xB) (-xB) (homogenizedNumerator P degree) /
          evalAt (zB - xB) (-xB) (denominator M K L)
        (xB, zB) = (-(Z ^ 2), X ^ 2 - Z ^ 2) ∧
        evalAt (zB - xB) (-xB) (denominator M K L) ≠ 0 ∧
        HasSum (fun i => ((I * Z) / X) *
          bJointTerm w u v (translatedDetector true N (Z ^ 2) b) (I * Z) (-D) i)
          (I * value) := by
  intro grade M K L N degree
  obtain ⟨P, hP, _, hRat⟩ := hhbb_marked_two_variable_common_rational
    slot colour n l hl hpar u v w b p q r d hu hv hw hb
  refine ⟨P, hP, ?_⟩
  intro X Z D hX y him hre hZ hD xB zB value
  have h := hRat X Z hX him hZ
  obtain ⟨hDs, hA⟩ := h.2.2.1 D hD hre
  have hxB : xB = -(Z ^ (2 : ℕ)) := by
    dsimp only [xB]
    rw [mul_pow, Complex.I_sq, neg_one_mul]
  have hzB : zB = X ^ (2 : ℕ) - Z ^ (2 : ℕ) := by
    simpa only [zB, neg_sq] using hDs
  have hx : zB - xB = X ^ (2 : ℕ) := by rw [hxB, hzB, sub_neg_eq_add, sub_add_cancel]
  have hz : -xB = Z ^ (2 : ℕ) := by rw [hxB, neg_neg]
  refine ⟨Prod.ext hxB hzB, by simpa only [hx, hz] using h.1, ?_⟩
  have hy₁ : 1 - y ≠ 0 := by
    intro he
    have hp : y = 1 := (sub_eq_zero.mp he).symm
    simp only [hp, Complex.one_im, lt_irrefl] at him
  have hd : D ≠ 0 := by
    intro hd
    rw [hd, zero_div] at hD
    exact hy₁ (by rw [← sqrt_square (1 - y), ← hD, zero_pow (by decide : (2 : ℕ) ≠ 0)])
  have hrad : ‖D‖ < ‖Z‖ := by
    have hrel : ‖D / X‖ < ‖Z / X‖ := by
      apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simpa only [hD, hZ, ← norm_pow, sqrt_square] using (norm_one_sub_lt_iff y).mpr hre
    rwa [norm_div, norm_div, div_lt_div_iff_of_pos_right (norm_pos_iff.mpr hX)] at hrel
  have hs := upper_fixed_d_joint_hasSum false true M K L N u v w b
    (hu.symm ▸ marked_grade slot colour n l .P p)
    (hv.symm ▸ marked_grade slot colour n l .Q q)
    (hw.symm ▸ marked_grade slot colour n l .R r)
    (hb.symm ▸ marked_grade slot colour n l .S d) hd hrad
  let b' := translatedDetector true N (Z ^ 2) b
  have hB : HasSum (bJointTerm w u v b' (I * Z) (-D))
      (∑' i, hhbbA u v w b D Z i) :=
    hs.congr_fun (fixed_d_neg_pair_root u v w b' D (I * Z))
  have hValue := hA.tsum_eq
  rw [tsum_mul_left] at hValue
  change (Z / X) * (∑' i, hhbbA u v w b D Z i) =
    evalAt (X ^ 2) (Z ^ 2) (homogenizedNumerator P degree) /
      evalAt (X ^ 2) (Z ^ 2) (denominator M K L) at hValue
  have hPhase : I * value = ((I * Z) / X) * ∑' i, hhbbA u v w b D Z i := by
    dsimp only [value]
    rw [hx, hz, ← hValue, ← mul_assoc, mul_div_assoc]
  rw [hPhase]
  exact hB.mul_left ((I * Z) / X)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBHHBRationalTransport
