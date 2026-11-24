/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHRealSewing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHRealSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-coordinate real sewing of the actual homogeneous Leech four-H matrix coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension

/-! Scalar sewing of the two actual Leech field compositions on `0 < z < x < 2z`.
The coordinates use positive real square roots and the coefficient fields retain
their upper-branch phases. Both series sum over all pairs of doubled modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open ActualEnergyRestrictedDual (maxOddWeight)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open HalfFock.ActualEnergyCovariance (correctedField_signed_output)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticePositiveEnergy (grade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven leechUnit)
open Orbifold.NativeFixedPairField (nu nu_coeff_of_grade nu_coeff_odd_zero nu_lower_truncation)
open Orbifold.NativeFixedPairState (fixedPairWeight fixedPairState_grade)
open Orbifold.NativeFixedUpperRightSkew
  (rightField rightField_coeff rightField_odd_zero R_pairing_finite)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeFourHUpperProduct (fixedBProductCoeff)
open NativeFourHHomogeneousExtension
  (homogeneousH_zero_of_odd_grade fourH_actual_A_eq_B_of_homogeneous)
open NativeMixedWickChartTransport (laurentRoot laurentRoot_values sigma)

open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private maxOddWeight_le_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm

local notation "ℒ" => leechData
local notation "√ℂ" r:arg => (Real.sqrt r : ℂ)

private def aCoeff (u v w b : TwistedEven) (j e : ℤ) : ℂ :=
  actualForm ℒ leechUnit b.val
    ((correctedField ℒ leechUnit ((nu false u).coeff j v).val).coeff e w.val)

private def bCoeff (u v w b : TwistedEven) (j e : ℤ) : ℂ :=
  actualForm ℒ leechUnit b.val
    ((rightField ℒ leechUnit false u).coeff e ((nu false v).coeff j w)).val

/-- The actual A iterate term at independent doubled exponents in `x-z` and `z`. -/
def realATerm (x z : ℝ) (u v w b : TwistedEven) (p : ℤ × ℤ) : ℂ :=
  aCoeff u v w b p.1 p.2 * ((√ℂ (x - z)) ^ p.1 * (√ℂ z) ^ p.2)

/-- The actual B product term at independent doubled exponents in `z` and `x`.
The fixed right field includes the upper half-turn and translation. -/
def realBTerm (x z : ℝ) (u v w b : TwistedEven) (p : ℤ × ℤ) : ℂ :=
  bCoeff u v w b p.1 p.2 * ((√ℂ z) ^ p.1 * (√ℂ x) ^ p.2)

/-- The continued real A matrix coefficient. -/
def actualA (x z : ℝ) (u v w b : TwistedEven) : ℂ :=
  ∑' p, realATerm x z u v w b p

/-- The continued real B matrix coefficient. -/
def actualB (x z : ℝ) (u v w b : TwistedEven) : ℂ :=
  ∑' p, realBTerm x z u v w b p

private theorem pair_off_energy (M K : ℕ) (u v : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) (j : ℤ)
    (hj : ∀ E : ℕ, j ≠ fixedAExponent M K E) : (nu false u).coeff j v = 0 := by
  by_cases hM : Even M
  · by_cases hK : Even K
    · by_cases he : Even j
      · have hbelow : j < -((M : ℤ) + K + 6) := by
          by_contra! h
          apply hj ((j + ((M : ℤ) + K + 6)) / 2).toNat
          obtain ⟨i, hi⟩ := he
          obtain ⟨m, hm⟩ := hM
          obtain ⟨k, hk⟩ := hK
          unfold fixedAExponent
          omega
        have hMu : (maxOddWeight ℒ leechUnit u.val : ℤ) ≤ M := by
          exact_mod_cast maxOddWeight_le_grade hu
        have hKv : (maxOddWeight ℒ leechUnit v.val : ℤ) ≤ K := by
          exact_mod_cast maxOddWeight_le_grade hv
        exact nu_lower_truncation false u v j (by omega)
      · exact nu_coeff_odd_zero false j u v (Int.not_even_iff_odd.mp he)
    · rw [homogeneousH_zero_of_odd_grade K v hv hK, map_zero]
  · simp [homogeneousH_zero_of_odd_grade M u hu hM]

private theorem pair_energy (M K E : ℕ) (u v : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    ((nu false u).coeff (fixedAExponent M K E) v).val ∈ grade ℒ (E : ℤ) := by
  by_cases he : Even (fixedAExponent M K E)
  · obtain ⟨k, hk⟩ := he
    let m : ℤ := -k - 1
    have hj : fixedAExponent M K E = -2 * m - 2 := by dsimp [m]; omega
    rw [hj, nu_coeff_of_grade false M K m u v hu hv]
    have he : fixedPairWeight M K m = (E : ℤ) := by
      unfold fixedAExponent at hj
      unfold fixedPairWeight
      omega
    rw [← he]
    exact fixedPairState_grade false M K m u v
  · rw [nu_coeff_odd_zero false _ u v (Int.not_even_iff_odd.mp he), Submodule.coe_zero]
    exact Submodule.zero_mem _

private theorem a_off_right (M K L N E : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (e : ℤ) (he : e ≠ (N : ℤ) - L - 2 * (E : ℤ)) :
    aCoeff u v w b (fixedAExponent M K E) e = 0 := by
  have hwL := (actualGrade_eigen ℒ leechUnit L w.val).mp hw
  have hbN := (actualGrade_eigen ℒ leechUnit N b.val).mp hb
  have hout := correctedField_signed_output ℒ leechUnit (E : ℤ) (L : ℤ) e _
    (pair_energy M K E u v hu hv) w.val (by simpa only [Int.cast_natCast] using hwL)
  exact actualForm_oddGrade_orthogonal ℒ leechUnit (N : ℤ) ((L : ℤ) + e + 2 * E)
    b.val _ (by simpa only [Int.cast_natCast] using hbN) hout (by omega)

private theorem b_off_right (M K L N E : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (e : ℤ) (he : e ≠ (N : ℤ) - M - 2 * (E : ℤ)) :
    bCoeff u v w b (fixedAExponent K L E) e = 0 := by
  unfold bCoeff
  by_cases heven : Even e
  · obtain ⟨k, hk⟩ := heven
    let m : ℤ := -k - 1
    have hm : e = -2 * m - 2 := by dsimp [m]; omega
    rw [hm, rightField_coeff, R_pairing_finite ℒ leechUnit false m N _ _ b.val hb]
    apply Finset.sum_eq_zero
    intro ell _
    have hbN := (actualGrade_eigen ℒ leechUnit N b.val).mp hb
    have huM := (actualGrade_eigen ℒ leechUnit M u.val).mp hu
    have hlow := lowering_eigen ℒ leechUnit (N : ℤ) b.val
      (by simpa only [Int.cast_natCast] using hbN) ell
    have hout := correctedField_signed_output ℒ leechUnit (E : ℤ) (M : ℤ)
      (-2 * (m + (ell : ℤ)) - 2) _ (pair_energy K L E v w hv hw) u.val
      (by simpa only [Int.cast_natCast] using huM)
    -- The shift by `-2 * ell` occurs on both sides of the pairing.
    rw [actualForm_oddGrade_orthogonal ℒ leechUnit _ _ ((T ℒ leechUnit ^ ell) b.val) _
      hlow hout (by omega), mul_zero]
  · rw [rightField_odd_zero ℒ leechUnit false e (Int.not_even_iff_odd.mp heven),
      Submodule.coe_zero, map_zero]

private def aModes (M K L N : ℕ) (j : ℤ) : ℤ × ℤ :=
  (j, (N : ℤ) - (L : ℤ) - (j + ((M : ℤ) + (K : ℤ) + 6)))

private def bModes (M K L N E : ℕ) : ℤ × ℤ :=
  (fixedAExponent K L E, (N : ℤ) - (M : ℤ) - 2 * (E : ℤ))

private theorem a_outside (M K L N : ℕ) (x z : ℝ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (p : ℤ × ℤ) (hp : p ∉ Set.range (aModes M K L N ∘ fixedAExponent M K)) :
    realATerm x z u v w b p = 0 := by
  rcases p with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = fixedAExponent M K E
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (N : ℤ) - L - 2 * (E : ℤ) := by
      intro he
      apply hp
      refine ⟨E, Prod.ext rfl ?_⟩
      dsimp [aModes, fixedAExponent] at *
      omega
    simp only [realATerm, a_off_right M K L N E u v w b hu hv hw hb e he, zero_mul]
  · simp only [not_exists] at hj
    simp [realATerm, aCoeff, pair_off_energy M K u v hu hv j hj]

private theorem b_outside (M K L N : ℕ) (x z : ℝ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (p : ℤ × ℤ) (hp : p ∉ Set.range (bModes M K L N)) : realBTerm x z u v w b p = 0 := by
  rcases p with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = fixedAExponent K L E
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (N : ℤ) - M - 2 * (E : ℤ) := by
      intro he
      exact hp ⟨E, Prod.ext rfl he.symm⟩
    simp only [realBTerm, b_off_right M K L N E u v w b hu hv hw hb e he, zero_mul]
  · simp only [not_exists] at hj
    simp [realBTerm, bCoeff, pair_off_energy K L v w hv hw j hj]

private theorem split_powers (a : ℂ) {r : ℝ} (hr : 0 < r) (j s : ℤ) :
    a ^ j * (√ℂ r) ^ (-2 * s - j) = (r : ℂ) ^ (-s) * (a / √ℂ r) ^ j := by
  have hroot : (√ℂ r) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hr).ne'
  have hsq : (√ℂ r) ^ (2 : ℤ) = (r : ℂ) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← Complex.ofReal_pow,
      Real.sq_sqrt hr.le]
  rw [zpow_sub₀ hroot, show -2 * s = 2 * -s by ring, zpow_mul, hsq, div_zpow]
  simp only [div_eq_mul_inv]
  ring

/-- On the positive real overlap the two actual field matrix coefficients
converge unconditionally and agree, including homogeneous zero inputs. -/
theorem fourH_actual_real_sewing (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {x z : ℝ} (hz : 0 < z) (hzx : z < x) (hxz : x < 2 * z) :
    Summable (realATerm x z u v w b) ∧ Summable (realBTerm x z u v w b) ∧
      actualA x z u v w b = actualB x z u v w b := by
  by_cases hzero : u = 0 ∨ v = 0 ∨ w = 0 ∨ b = 0
  · have hAzero : realATerm x z u v w b = 0 := by
      funext p
      rcases hzero with rfl | rfl | rfl | rfl <;> simp [realATerm, aCoeff]
    have hBzero : realBTerm x z u v w b = 0 := by
      funext p
      rcases hzero with rfl | rfl | rfl | rfl <;> simp [realBTerm, bCoeff]
    have hsum : Summable (0 : ℤ × ℤ → ℂ) :=
      (summable_zero : Summable (fun _ : ℤ × ℤ => (0 : ℂ)))
    rw [hAzero, hBzero]
    exact ⟨hsum, hsum, by simp [actualA, actualB, hAzero, hBzero]⟩
  push Not at hzero
  obtain ⟨⟨m, hm⟩, ⟨k, hk⟩, ⟨l, hl⟩, ⟨n, hn⟩⟩ :
      Even M ∧ Even K ∧ Even L ∧ Even N :=
    ⟨by_contra fun h => hzero.1 (homogeneousH_zero_of_odd_grade M u hu h),
     by_contra fun h => hzero.2.1 (homogeneousH_zero_of_odd_grade K v hv h),
     by_contra fun h => hzero.2.2.1 (homogeneousH_zero_of_odd_grade L w hw h),
     by_contra fun h => hzero.2.2.2 (homogeneousH_zero_of_odd_grade N b hb h)⟩
  let s := sigma (M : ℤ) K L N
  have hs : -2 * s = (N : ℤ) - (6 + (M : ℤ) + K + L) := by
    dsimp [s, sigma]
    omega
  have hx : 0 < x := hz.trans hzx
  let y := z / x
  have hy : (1 / 2 : ℝ) < y := (lt_div_iff₀ hx).2 (by linarith)
  have hy₁ : y < 1 := (div_lt_one hx).2 hzx
  have hAratio : (√ℂ (x - z)) / (√ℂ z) = laurentRoot .A y := by
    rw [(laurentRoot_values hy₁).1, ← Complex.ofReal_div, ← Real.sqrt_div (sub_nonneg.mpr hzx.le)]
    have hratio : (x - z) / z = (1 - y) / y := by
      dsimp [y]
      field_simp
    rw [hratio]
  have hBratio : (√ℂ z) / (√ℂ x) = √ℂ y := by
    rw [← Complex.ofReal_div, ← Real.sqrt_div hz.le]
  let A (j : ℤ) := fixedAIterateCoeff false M K L N j u v w.val b.val * laurentRoot .A y ^ j
  let B (E : ℕ) := fixedBProductCoeff false false M K L N v w u b E *
    (√ℂ y) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L))
  obtain ⟨hA, hB, hcompare⟩ : Summable A ∧ Summable B ∧
      (∑' j, A j) = (y : ℂ) ^ s * ∑' E, B E :=
    fourH_actual_A_eq_B_of_homogeneous M K L N u v w b hu hv hw hb hy hy₁
  have hAdiag (j : ℤ) :
      realATerm x z u v w b (aModes M K L N j) = (z : ℂ) ^ (-s) * A j := by
    change fixedAIterateCoeff false M K L N j u v w.val b.val *
      ((√ℂ (x - z)) ^ j * (√ℂ z) ^ ((N : ℤ) - L - (j + ((M : ℤ) + K + 6)))) = _
    rw [show (N : ℤ) - L - (j + ((M : ℤ) + K + 6)) = -2 * s - j by omega,
      split_powers _ hz, hAratio]
    dsimp [A]
    ring
  have hBdiag (E : ℕ) :
      realBTerm x z u v w b (bModes M K L N E) = (x : ℂ) ^ (-s) * B E := by
    let j := fixedAExponent K L E
    have hj : j = 2 * (E : ℤ) - (6 + (K : ℤ) + L) := by unfold j fixedAExponent; ring
    have hright : (N : ℤ) - M - 2 * (E : ℤ) = -2 * s - j := by omega
    have hcoeff : bCoeff u v w b j ((N : ℤ) - M - 2 * (E : ℤ)) =
        fixedBProductCoeff false false M K L N v w u b E := by
      rw [hj]
      rfl
    change bCoeff u v w b j ((N : ℤ) - M - 2 * (E : ℤ)) *
      ((√ℂ z) ^ j * (√ℂ x) ^ ((N : ℤ) - M - 2 * (E : ℤ))) = _
    rw [hcoeff, hright, split_powers _ hx, hBratio, hj]
    dsimp [B]
    ring
  have haInj : Function.Injective (aModes M K L N) := fun _ _ h => congrArg Prod.fst h
  have hbInj : Function.Injective (bModes M K L N) := by
    intro E F h
    have hEF := congrArg Prod.snd h
    dsimp [bModes] at hEF
    omega
  have haOff (p : ℤ × ℤ) (hp : p ∉ Set.range (aModes M K L N)) : realATerm x z u v w b p = 0 :=
    a_outside M K L N x z u v w b hu hv hw hb p
      (fun ⟨E, he⟩ => hp ⟨fixedAExponent M K E, he⟩)
  have haSum := (haInj.hasSum_iff haOff).mp
    ((hA.hasSum.mul_left ((z : ℂ) ^ (-s))).congr_fun hAdiag)
  have hbSum := (hbInj.hasSum_iff (b_outside M K L N x z u v w b hu hv hw hb)).mp
    ((hB.hasSum.mul_left ((x : ℂ) ^ (-s))).congr_fun hBdiag)
  refine ⟨haSum.summable, hbSum.summable, ?_⟩
  rw [actualA, actualB, haSum.tsum_eq, hbSum.tsum_eq, hcompare, ← mul_assoc]
  have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  rw [show (y : ℂ) = (z : ℂ) / (x : ℂ) from Complex.ofReal_div _ _, div_zpow,
    ← mul_div_assoc, ← zpow_add₀ hzC, neg_add_cancel, zpow_zero, one_div, zpow_neg]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
