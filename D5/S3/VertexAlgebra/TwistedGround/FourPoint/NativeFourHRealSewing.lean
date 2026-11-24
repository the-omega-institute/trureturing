/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHRealSewing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHRealSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-coordinate real sewing of the actual homogeneous Leech four-H matrix coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Convex

/-! Scalar sewing of the two actual Leech field compositions on `0 < z < x < 2z`.
The coordinates use positive real square roots and the coefficient fields retain
their upper-branch phases. The complex extension uses integral powers on the
even support. Both series sum over all pairs of doubled modes. -/

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

private theorem a_outside (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (p : ℤ × ℤ) (hp : p ∉ Set.range (aModes M K L N ∘ fixedAExponent M K)) :
    aCoeff u v w b p.1 p.2 = 0 := by
  rcases p with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = fixedAExponent M K E
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (N : ℤ) - L - 2 * (E : ℤ) := by
      intro he
      apply hp
      refine ⟨E, Prod.ext rfl ?_⟩
      dsimp [aModes, fixedAExponent] at *
      omega
    exact a_off_right M K L N E u v w b hu hv hw hb e he
  · simp only [not_exists] at hj
    simp [aCoeff, pair_off_energy M K u v hu hv j hj]

private theorem b_outside (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (p : ℤ × ℤ) (hp : p ∉ Set.range (bModes M K L N)) :
    bCoeff u v w b p.1 p.2 = 0 := by
  rcases p with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = fixedAExponent K L E
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (N : ℤ) - M - 2 * (E : ℤ) := by
      intro he
      exact hp ⟨E, Prod.ext rfl he.symm⟩
    exact b_off_right M K L N E u v w b hu hv hw hb e he
  · simp only [not_exists] at hj
    simp [bCoeff, pair_off_energy K L v w hv hw j hj]

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
  have haOff (p : ℤ × ℤ) (hp : p ∉ Set.range (aModes M K L N)) :
      realATerm x z u v w b p = 0 := by
    rw [realATerm, a_outside M K L N u v w b hu hv hw hb p
      (fun ⟨E, he⟩ => hp ⟨fixedAExponent M K E, he⟩), zero_mul]
  have hbOff (p : ℤ × ℤ) (hp : p ∉ Set.range (bModes M K L N)) :
      realBTerm x z u v w b p = 0 := by
    rw [realBTerm, b_outside M K L N u v w b hu hv hw hb p hp, zero_mul]
  have haSum := (haInj.hasSum_iff haOff).mp
    ((hA.hasSum.mul_left ((z : ℂ) ^ (-s))).congr_fun hAdiag)
  have hbSum := (hbInj.hasSum_iff hbOff).mp
    ((hB.hasSum.mul_left ((x : ℂ) ^ (-s))).congr_fun hBdiag)
  refine ⟨haSum.summable, hbSum.summable, ?_⟩
  rw [actualA, actualB, haSum.tsum_eq, hbSum.tsum_eq, hcompare, ← mul_assoc]
  have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  rw [show (y : ℂ) = (z : ℂ) / (x : ℂ) from Complex.ofReal_div _ _, div_zpow,
    ← mul_div_assoc, ← zpow_add₀ hzC, neg_add_cancel, zpow_zero, one_div, zpow_neg]

open scoped Topology ENNReal NNReal

private def integralTerm (c : ℤ × ℤ → ℂ) (a b : ℂ) (p : ℤ × ℤ) : ℂ :=
  c p * (a ^ (p.1 / 2) * b ^ (p.2 / 2))

/-- The raw A iterate term with integral powers on its even doubled-mode support. -/
def complexATerm (x z : ℂ) (u v w b : TwistedEven) (p : ℤ × ℤ) : ℂ :=
  integralTerm (fun q => aCoeff u v w b q.1 q.2) (x - z) z p

/-- The raw B product term with integral powers and the upper right field coefficient. -/
def complexBTerm (x z : ℂ) (u v w b : TwistedEven) (p : ℤ × ℤ) : ℂ :=
  integralTerm (fun q => bCoeff u v w b q.1 q.2) z x p

-- The index starts at energy zero, and the two halved exponents sum to `d`.
private def energyModes (d i : ℤ) (E : ℕ) : ℤ × ℤ :=
  (2 * ((E : ℤ) - i), 2 * (d - ((E : ℤ) - i)))

private theorem energyModes_injective (d i : ℤ) : Function.Injective (energyModes d i) := by
  intro E F h
  have hfst := congrArg Prod.fst h
  dsimp [energyModes] at hfst
  omega

private theorem sqrt_zpow_double {a : ℝ} (ha : 0 ≤ a) (j : ℤ) :
    (√ℂ a) ^ (2 * j) = (a : ℂ) ^ j := by
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast,
    ← Complex.ofReal_pow, Real.sq_sqrt ha]

private theorem integralTerm_ofReal (c : ℤ × ℤ → ℂ) (d i : ℤ)
    (hoff : ∀ p, p ∉ Set.range (energyModes d i) → c p = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℤ × ℤ) :
    integralTerm c (a : ℂ) (b : ℂ) p = c p * ((√ℂ a) ^ p.1 * (√ℂ b) ^ p.2) := by
  by_cases hp : p ∈ Set.range (energyModes d i)
  · obtain ⟨E, rfl⟩ := hp
    dsimp [integralTerm, energyModes]
    rw [sqrt_zpow_double ha, sqrt_zpow_double hb,
      show (2 * ((E : ℤ) - i)) / 2 = (E : ℤ) - i by omega,
      show (2 * (d - ((E : ℤ) - i))) / 2 = d - ((E : ℤ) - i) by omega]
  · simp [integralTerm, hoff p hp]

private theorem integralTerm_energy (c : ℤ × ℤ → ℂ) (d i : ℤ) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (E : ℕ) :
    integralTerm c a b (energyModes d i E) =
      (b ^ d * (a / b) ^ (-i)) * (c (energyModes d i E) * (a / b) ^ E) := by
  have hpow : (a / b) ^ (-i) * (a / b) ^ E = a ^ ((E : ℤ) - i) / b ^ ((E : ℤ) - i) := by
    rw [← zpow_natCast (a / b) E, ← zpow_add₀ (div_ne_zero ha hb),
      show -i + (E : ℤ) = (E : ℤ) - i by omega, div_zpow]
  unfold integralTerm
  rw [show (energyModes d i E).1 / 2 = (E : ℤ) - i by unfold energyModes; omega,
    show (energyModes d i E).2 / 2 = d - ((E : ℤ) - i) by unfold energyModes; omega,
    zpow_sub₀ hb]
  calc
    _ = b ^ d * c (energyModes d i E) * (a ^ ((E : ℤ) - i) / b ^ ((E : ℤ) - i)) := by ring
    _ = _ := by rw [← hpow]; ring

private theorem summable_at_ratio (c : ℤ × ℤ → ℂ) (d i : ℤ) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : Summable (integralTerm c a b)) :
    Summable (fun E : ℕ => c (energyModes d i E) * (a / b) ^ E) := by
  have h := hs.comp_injective (energyModes_injective d i)
  have hfactor := mul_ne_zero (zpow_ne_zero d hb) (zpow_ne_zero (-i) (div_ne_zero ha hb))
  apply (summable_mul_left_iff hfactor).mp
  exact h.congr (integralTerm_energy c d i ha hb)

private theorem radialSeries_radius (c : ℕ → ℂ)
    (hs : ∀ r : ℝ, 1 / 2 < r → r < 1 → Summable (fun E : ℕ => c E * (r : ℂ) ^ E)) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr₁ : r < 1 := by exact_mod_cast hr
  obtain ⟨ρ, hρ, hρ₁⟩ := exists_between (max_lt hr₁ (show (1 / 2 : ℝ≥0) < 1 by norm_num))
  have hhalf : (1 / 2 : ℝ) < (ρ : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (le_max_right r (1 / 2)) hρ
  have hlt : (ρ : ℝ) < 1 := by exact_mod_cast hρ₁
  have habs := (hs ρ hhalf hlt).norm
  have hle : (ρ : ℝ≥0∞) ≤ p.radius := p.le_radius_of_summable_norm (by
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ρ.coe_nonneg] using habs)
  exact (ENNReal.coe_le_coe.mpr ((le_max_left _ _).trans hρ.le)).trans hle

private theorem eball_of_norm_lt_one {y : ℂ} (hy : ‖y‖ < 1) :
    y ∈ Metric.eball (0 : ℂ) 1 := by
  rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

private theorem laurentSeries_analyticAt (c : ℕ → ℂ) (i : ℤ)
    (hc : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius)
    {y : ℂ} (hy : ‖y‖ < 1) (hy₀ : y ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => w ^ (-i) * FormalMultilinearSeries.ofScalarsSum c w) y := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hpos : 0 < p.radius := lt_of_lt_of_le zero_lt_one hc
  exact (analyticAt_id.zpow hy₀).mul ((p.hasFPowerSeriesOnBall hpos).analyticOnNhd y
    (Metric.eball_subset_eball hc (eball_of_norm_lt_one hy)))

private theorem integralTerm_hasSum (c : ℤ × ℤ → ℂ) (d i : ℤ)
    (hoff : ∀ p, p ∉ Set.range (energyModes d i) → c p = 0)
    (hc : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ (c ∘ energyModes d i)).radius)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : ‖a / b‖ < 1) :
    HasSum (integralTerm c a b)
      (b ^ d * (a / b) ^ (-i) *
        FormalMultilinearSeries.ofScalarsSum (c ∘ energyModes d i) (a / b)) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (c ∘ energyModes d i)
  have h := p.hasSum (Metric.eball_subset_eball hc (eball_of_norm_lt_one hr))
  apply ((energyModes_injective d i).hasSum_iff
    (fun q hq => show integralTerm c a b q = 0 by simp [integralTerm, hoff q hq])).mp
  refine h.mul_left _ |>.congr_fun ?_
  intro E
  change integralTerm c a b (energyModes d i E) = _ * ((FormalMultilinearSeries.ofScalars ℂ
    (c ∘ energyModes d i)) E (fun _ => a / b))
  rw [integralTerm_energy c d i ha hb, FormalMultilinearSeries.ofScalars_apply_eq]
  rfl

private theorem norm_one_sub_lt_iff (y : ℂ) : ‖1 - y‖ < ‖y‖ ↔ (1 / 2 : ℝ) < y.re := by
  rw [← sq_lt_sq₀ (norm_nonneg (1 - y)) (norm_nonneg y), Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

private theorem ratio_analytic {y : ℂ} (hy : y ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => (1 - w) / w) y :=
  (analyticAt_const.sub analyticAt_id).div analyticAt_id hy

private theorem sewing_on_cap (f g : ℂ → ℂ)
    (hf : ∀ y : ℂ, ‖y‖ < 1 → 1 / 2 < y.re → AnalyticAt ℂ f y)
    (hg : ∀ y : ℂ, ‖y‖ < 1 → 1 / 2 < y.re → AnalyticAt ℂ g y)
    (hreal : ∀ r : ℝ, 1 / 2 < r → r < 1 → f (r : ℂ) = g (r : ℂ)) :
    ∀ y : ℂ, ‖y‖ < 1 → 1 / 2 < y.re → f y = g y := by
  let U := Metric.ball (0 : ℂ) 1 ∩ {y : ℂ | (1 / 2 : ℝ) < y.re}
  have hU : IsPreconnected U :=
    ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt _)).isPreconnected
  have hfU : AnalyticOnNhd ℂ f U := fun y hy => hf y (by simpa using hy.1) hy.2
  have hgU : AnalyticOnNhd ℂ g U := fun y hy => hg y (by simpa using hy.1) hy.2
  let r₀ : ℝ := 3 / 4
  have hr₀ : (r₀ : ℂ) ∈ U := by
    change (r₀ : ℂ) ∈ Metric.ball 0 1 ∧ (1 / 2 : ℝ) < (r₀ : ℂ).re
    norm_num [Metric.mem_ball, r₀, Complex.norm_real]
  have hacc : (r₀ : ℂ) ∈ closure ({y | f y = g y} \ {(r₀ : ℂ)}) := by
    have hr : r₀ ∈ closure (Set.Ioo r₀ (1 : ℝ)) := by
      rw [closure_Ioo (by norm_num [r₀] : r₀ ≠ 1)]
      exact ⟨le_rfl, by norm_num [r₀]⟩
    apply closure_mono _ (mem_closure_image Complex.continuous_ofReal.continuousAt hr)
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨hreal r (lt_trans (by norm_num [r₀] : (1 / 2 : ℝ) < r₀) hr.1) hr.2, ?_⟩
    simpa using hr.1.ne'
  have hEq := hfU.eqOn_of_preconnected_of_mem_closure hgU hU hr₀ hacc
  exact fun y hy hre => hEq ⟨by simpa using hy, hre⟩

private theorem sew_integral_terms (cA cB : ℤ × ℤ → ℂ) (d iA iB : ℤ)
    (haOff : ∀ p, p ∉ Set.range (energyModes d iA) → cA p = 0)
    (hbOff : ∀ p, p ∉ Set.range (energyModes d iB) → cB p = 0)
    (hreal : ∀ {x z : ℝ}, 0 < z → z < x → x < 2 * z →
      Summable (integralTerm cA ((x : ℂ) - z) z) ∧
      Summable (integralTerm cB (z : ℂ) x) ∧
      (∑' p, integralTerm cA ((x : ℂ) - z) z p) = ∑' p, integralTerm cB (z : ℂ) x p)
    {x z : ℂ} (hx : x ≠ 0) (hzx : ‖z‖ < ‖x‖) (hxz : ‖x - z‖ < ‖z‖) :
    ∃ s : ℂ, HasSum (integralTerm cA (x - z) z) s ∧ HasSum (integralTerm cB z x) s := by
  have hradA : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ (cA ∘ energyModes d iA)).radius := by
    apply radialSeries_radius
    intro r hr hr₁
    have hp : 0 < r := by linarith
    have hs := (hreal (x := 1 + r) (z := 1) zero_lt_one (by linarith) (by linarith)).1
    have hs' : Summable (integralTerm cA (r : ℂ) 1) := by push_cast at hs; simpa using hs
    simpa [Function.comp_def] using
      summable_at_ratio cA d iA (Complex.ofReal_ne_zero.mpr hp.ne') one_ne_zero hs'
  have hradB : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ (cB ∘ energyModes d iB)).radius := by
    apply radialSeries_radius
    intro r hr hr₁
    have hp : 0 < r := by linarith
    have hs : Summable (integralTerm cB (r : ℂ) 1) := by
      simpa using (hreal (x := 1) (z := r) hp hr₁ (by linarith)).2.1
    simpa [Function.comp_def] using
      summable_at_ratio cB d iB (Complex.ofReal_ne_zero.mpr hp.ne') one_ne_zero hs
  let A : ℂ → ℂ := FormalMultilinearSeries.ofScalarsSum (cA ∘ energyModes d iA)
  let B : ℂ → ℂ := FormalMultilinearSeries.ofScalarsSum (cB ∘ energyModes d iB)
  let t (y : ℂ) := (1 - y) / y
  let f (y : ℂ) := y ^ d * (t y ^ (-iA) * A (t y))
  let g (y : ℂ) := y ^ (-iB) * B y
  have cap_y_ne {y : ℂ} (hre : (1 / 2 : ℝ) < y.re) : y ≠ 0 := by
    rintro rfl
    norm_num at hre
  have cap_sub_ne {y : ℂ} (hy : ‖y‖ < 1) : 1 - y ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hy
    exact (lt_irrefl 1) hy
  have cap_ratio {y : ℂ} (hre : (1 / 2 : ℝ) < y.re) : ‖t y‖ < 1 := by
    change ‖(1 - y) / y‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (cap_y_ne hre))]
    exact (norm_one_sub_lt_iff y).mpr hre
  have hf (y : ℂ) (hy : ‖y‖ < 1) (hre : 1 / 2 < y.re) : AnalyticAt ℂ f y := by
    have ht : AnalyticAt ℂ t y := ratio_analytic (cap_y_ne hre)
    have ht₀ : t y ≠ 0 := div_ne_zero (cap_sub_ne hy) (cap_y_ne hre)
    exact (analyticAt_id.zpow (cap_y_ne hre)).mul
      ((laurentSeries_analyticAt _ iA hradA (cap_ratio hre) ht₀).comp ht)
  have hg (y : ℂ) (hy : ‖y‖ < 1) (hre : 1 / 2 < y.re) : AnalyticAt ℂ g y :=
    laurentSeries_analyticAt _ iB hradB hy (cap_y_ne hre)
  have hEq : ∀ y : ℂ, ‖y‖ < 1 → 1 / 2 < y.re → f y = g y := by
    apply sewing_on_cap f g hf hg
    intro r hr hr₁
    have hp : 0 < r := by linarith
    have hnorm : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hp] using hr₁
    have hA : HasSum (integralTerm cA (1 - (r : ℂ)) (r : ℂ)) (f (r : ℂ)) :=
      by simpa only [f, A, t, mul_assoc] using
        integralTerm_hasSum cA d iA haOff hradA (cap_sub_ne hnorm) (cap_y_ne hr) (cap_ratio hr)
    have hB : HasSum (integralTerm cB (r : ℂ) 1) (g (r : ℂ)) := by
      simpa [g, B] using integralTerm_hasSum cB d iB hbOff hradB
        (cap_y_ne hr) one_ne_zero (by simpa using hnorm)
    have he := (hreal (x := 1) (z := r) hp hr₁ (by linarith)).2.2
    rw [Complex.ofReal_one, hA.tsum_eq, hB.tsum_eq] at he
    exact he
  let y := z / x
  have hz : z ≠ 0 := by
    rintro rfl
    simp only [sub_zero, norm_zero] at hxz
    exact (not_lt_of_ge (norm_nonneg x)) hxz
  have hy : ‖y‖ < 1 := by
    change ‖z / x‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hx)]
    exact hzx
  have hratio : (x - z) / z = t y := by
    dsimp [t, y]
    field_simp
  have hre : (1 / 2 : ℝ) < y.re := by
    apply (norm_one_sub_lt_iff y).mp
    have he : 1 - y = (x - z) / x := by
      change 1 - z / x = (x - z) / x
      rw [sub_div, div_self hx]
    rw [he]
    change ‖(x - z) / x‖ < ‖z / x‖
    rw [norm_div, norm_div]
    exact div_lt_div_of_pos_right hxz (norm_pos_iff.mpr hx)
  have hAz := integralTerm_hasSum cA d iA haOff hradA
    (sub_ne_zero.mpr (fun h => (ne_of_lt hzx) (congrArg norm h.symm))) hz
    (by rw [hratio]; exact cap_ratio hre)
  have hBz := integralTerm_hasSum cB d iB hbOff hradB hz hx hy
  have hscale : z = x * y := by
    change z = x * (z / x)
    field_simp
  have hscale_pow : z ^ d = x ^ d * y ^ d := by rw [← mul_zpow, ← hscale]
  have hAz' : HasSum (integralTerm cA (x - z) z) (x ^ d * f y) := by
    convert hAz using 1
    rw [hratio, hscale_pow]
    dsimp [f, A]
    ring
  refine ⟨x ^ d * f y, hAz', ?_⟩
  rw [hEq y hy hre]
  simpa only [g, B, y, mul_assoc] using hBz

/-- The actual A and upper B four-H matrix coefficients sew on the complex
common radial domain. Both sums retain their full pair of doubled mode indices.
A nonzero term has even doubled exponents and lies on the indicated energy diagonal. -/
theorem fourH_actual_complex_sewing (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {x z : ℂ} (hx : x ≠ 0) (hzx : ‖z‖ < ‖x‖) (hxz : ‖x - z‖ < ‖z‖) :
    Summable (complexATerm x z u v w b) ∧ Summable (complexBTerm x z u v w b) ∧
      (∑' p, complexATerm x z u v w b p) = (∑' p, complexBTerm x z u v w b p) ∧
      (∀ p, complexATerm x z u v w b p ≠ 0 → Even p.1 ∧ Even p.2 ∧
        ∃ E : ℕ, p = (fixedAExponent M K E, (N : ℤ) - L - 2 * (E : ℤ))) ∧
      (∀ p, complexBTerm x z u v w b p ≠ 0 → Even p.1 ∧ Even p.2 ∧
        ∃ E : ℕ, p = (fixedAExponent K L E, (N : ℤ) - M - 2 * (E : ℤ))) := by
  by_cases hzero : u = 0 ∨ v = 0 ∨ w = 0 ∨ b = 0
  · have hA : complexATerm x z u v w b = fun _ => 0 := by
      funext p
      rcases hzero with rfl | rfl | rfl | rfl <;> simp [complexATerm, integralTerm, aCoeff]
    have hB : complexBTerm x z u v w b = fun _ => 0 := by
      funext p
      rcases hzero with rfl | rfl | rfl | rfl <;> simp [complexBTerm, integralTerm, bCoeff]
    simp [hA, hB]
  push Not at hzero
  obtain ⟨⟨m, hm⟩, ⟨k, hk⟩, ⟨l, hl⟩, ⟨n, hn⟩⟩ : Even M ∧ Even K ∧ Even L ∧ Even N :=
    ⟨by_contra fun h => hzero.1 (homogeneousH_zero_of_odd_grade M u hu h),
     by_contra fun h => hzero.2.1 (homogeneousH_zero_of_odd_grade K v hv h),
     by_contra fun h => hzero.2.2.1 (homogeneousH_zero_of_odd_grade L w hw h),
     by_contra fun h => hzero.2.2.2 (homogeneousH_zero_of_odd_grade N b hb h)⟩
  let d : ℤ := (n : ℤ) - m - k - l - 3
  let iA : ℤ := (m : ℤ) + k + 3
  let iB : ℤ := (k : ℤ) + l + 3
  let cA (p : ℤ × ℤ) := aCoeff u v w b p.1 p.2
  let cB (p : ℤ × ℤ) := bCoeff u v w b p.1 p.2
  have hA_mode (E : ℕ) : energyModes d iA E = (aModes M K L N ∘ fixedAExponent M K) E := by
    apply Prod.ext <;> simp [energyModes, d, iA, aModes, fixedAExponent, hm, hk, hl, hn] <;> omega
  have hB_mode (E : ℕ) : energyModes d iB E = bModes M K L N E := by
    apply Prod.ext <;> simp [energyModes, d, iB, bModes, fixedAExponent, hm, hk, hl, hn] <;> omega
  have haOff (p : ℤ × ℤ) (hp : p ∉ Set.range (energyModes d iA)) : cA p = 0 := by
    apply a_outside M K L N u v w b hu hv hw hb p
    rintro ⟨E, hE⟩
    exact hp ⟨E, (hA_mode E).trans hE⟩
  have hbOff (p : ℤ × ℤ) (hp : p ∉ Set.range (energyModes d iB)) : cB p = 0 := by
    apply b_outside M K L N u v w b hu hv hw hb p
    rintro ⟨E, hE⟩
    exact hp ⟨E, (hB_mode E).trans hE⟩
  have hreal {r s : ℝ} (hs : 0 < s) (hsr : s < r) (hrs : r < 2 * s) :
      Summable (integralTerm cA ((r : ℂ) - s) s) ∧
      Summable (integralTerm cB (s : ℂ) r) ∧
      (∑' p, integralTerm cA ((r : ℂ) - s) s p) = ∑' p, integralTerm cB (s : ℂ) r p := by
    have hA : integralTerm cA ((r : ℂ) - s) s = realATerm r s u v w b := by
      funext p
      rw [← Complex.ofReal_sub]
      exact integralTerm_ofReal cA d iA haOff (sub_nonneg.mpr hsr.le) hs.le p
    have hB : integralTerm cB (s : ℂ) r = realBTerm r s u v w b :=
      funext (integralTerm_ofReal cB d iB hbOff hs.le (hs.trans hsr).le)
    rw [hA, hB]
    exact fourH_actual_real_sewing M K L N u v w b hu hv hw hb hs hsr hrs
  obtain ⟨s, haSum, hbSum⟩ := sew_integral_terms cA cB d iA iB haOff hbOff hreal hx hzx hxz
  refine ⟨haSum.summable, hbSum.summable, haSum.tsum_eq.trans hbSum.tsum_eq.symm, ?_, ?_⟩
  · intro p hp
    have hmem : p ∈ Set.range (energyModes d iA) := by
      by_contra h
      simp [complexATerm, integralTerm, show aCoeff u v w b p.1 p.2 = 0 from haOff p h] at hp
    obtain ⟨E, rfl⟩ := hmem
    refine ⟨even_two_mul _, even_two_mul _, E, ?_⟩
    rw [hA_mode]
    apply Prod.ext <;> simp [aModes, fixedAExponent]
  · intro p hp
    have hmem : p ∈ Set.range (energyModes d iB) := by
      by_contra h
      simp [complexBTerm, integralTerm, show bCoeff u v w b p.1 p.2 = 0 from hbOff p h] at hp
    obtain ⟨E, rfl⟩ := hmem
    exact ⟨even_two_mul _, even_two_mul _, E, hB_mode E⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
