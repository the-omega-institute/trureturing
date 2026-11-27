/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedPhysicalIterateInversion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedPhysicalIterateInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Detector reversal of the native mixed A iterate at the two physical root lifts. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateRadialInversion

/-! Reindex the actual two-mode sum by energy, then transport the normalized
inversion to the reciprocal roots with the same phase and divided lowerings
as in the native B-product reversal. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalIterateInversion

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeDetectorTranslation (detector_apply)
open Orbifold.NativeMixedPairSkew (swapInput)
open Orbifold.NativeMixedIterateInversionCoefficient (aCoeff)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedWickCuspGerm (mixedFieldLaurent mixedFieldLaurent_coeff)
open NativeMixedIterateInversionGerm (binomialExponent)
open NativeMixedIterateRadialInversion (aCoeff_inversion_hasSum_unit_disk)

open private mixed_a_off_diagonal aModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedAIterateRadial
open private mixedExponent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private opposite_grade_parities from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private descend_grade swapped_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
open private exchangedCoeff factorials one_add_re_pos from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm
open private aCoeff_summable from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateRadialInversion

local notation "ℒ" => leechData
local notation "T" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev weight (M : ℕ) : ℤ := 3 + (M : ℤ)

private abbrev aPrefactor (mP mQ mR mS : ℤ) (d z : ℂ) : ℂ :=
  d ^ (-(mP + mQ)) * z ^ (mS - mR)

private theorem ratio_pow (d z : ℂ) (n : ℕ) :
    ((d / z) ^ 2) ^ n = d ^ (2 * (n : ℤ)) * z ^ (-(2 * (n : ℤ))) := by
  rw [← zpow_natCast _ n, ← zpow_ofNat (d / z) 2, ← zpow_mul (d / z) 2 (n : ℤ),
    div_zpow, div_eq_mul_inv, zpow_neg]

/-- The literal double sum is equivalent to the normalized detector series
with its common Laurent monomial restored. Zero inputs can have any assigned
homogeneous grade. -/
theorem aJoint_hasSum_iff_energy (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {d z : ℂ} (hd : d ≠ 0) (hz : z ≠ 0) (value : ℂ) :
    HasSum (fun E : ℕ => aCoeff s t (weight M) (weight K) (weight H) (weight J) E
        P Q R S * ((d / z) ^ 2) ^ E) value ↔
      HasSum (aJointTerm s P Q R.val S.val d z)
        (aPrefactor (weight M) (weight K) (weight H) (weight J) d z * value) := by
  let modes (E : ℕ) : ℤ × ℤ :=
    (2 * (E : ℤ) - weight M - weight K, weight J - weight H - 2 * (E : ℤ))
  have hinj : Function.Injective modes := by
    intro E F h
    have hfirst := congrArg Prod.fst h
    dsimp only [modes] at hfirst
    omega
  have hoff (p : ℤ × ℤ) (hp : p ∉ Set.range modes) :
      aJointTerm s P Q R.val S.val d z p = 0 := by
    by_cases hzero : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0
    · rcases hzero with rfl | rfl | rfl | rfl
      · simp [← aModeLinear_apply s t]
      · simp [← aModeLinear_apply s t]
      · simp [aJointTerm]
      · simp [aJointTerm]
    push Not at hzero
    obtain ⟨hP₀, hQ₀, _, _⟩ := hzero
    have hpar := (opposite_grade_parities P Q hP hQ hP₀ hQ₀).1
    rcases p with ⟨j, e⟩
    by_cases he : e = (J : ℤ) - H - (j + (M : ℤ) + K + 6)
    · have hj : j ∉ Set.range (mixedExponent M K) := by
        rintro ⟨E, hE⟩
        change 2 * (E : ℤ) - ((M : ℤ) + K + 6) = j at hE
        apply hp
        refine ⟨E, Prod.ext ?_ ?_⟩
        · change 2 * (E : ℤ) - weight M - weight K = j
          dsimp only [weight]
          omega
        · change weight J - weight H - 2 * (E : ℤ) = e
          dsimp only [weight]
          omega
      have hc := mixedFieldLaurent_coeff s M K H J j P Q R.val S.val hP hQ hpar
      rw [mixedFieldLaurent, HahnSeries.embDomain_of_notMem_range hj] at hc
      rw [aJointTerm, he, ← hc, zero_mul]
    · rw [aJointTerm, mixed_a_off_diagonal s M K H J P Q R.val S.val hP hQ hR hS hpar j e he,
        zero_mul]
  let A := aPrefactor (weight M) (weight K) (weight H) (weight J) d z
  let f (E : ℕ) := aCoeff s t (weight M) (weight K) (weight H) (weight J) E
    P Q R S * ((d / z) ^ 2) ^ E
  have hA : A ≠ 0 := mul_ne_zero (zpow_ne_zero _ hd) (zpow_ne_zero _ hz)
  have hterm (E : ℕ) : (aJointTerm s P Q R.val S.val d z ∘ modes) E = A * f E := by
    have hpow : d ^ (modes E).1 * z ^ (modes E).2 = A * (((d / z) ^ 2) ^ E) := by
      change d ^ (2 * (E : ℤ) - weight M - weight K) *
        z ^ (weight J - weight H - 2 * (E : ℤ)) = _
      rw [show 2 * (E : ℤ) - weight M - weight K =
        -(weight M + weight K) + 2 * (E : ℤ) by ring,
        show weight J - weight H - 2 * (E : ℤ) =
          (weight J - weight H) + -(2 * (E : ℤ)) by ring,
        zpow_add₀ hd, zpow_add₀ hz, ratio_pow]
      dsimp only [A, aPrefactor]
      ring
    change aJointTerm s P Q R.val S.val d z (modes E) = A * f E
    rw [aJointTerm, hpow]
    simp only [modes, f, aCoeff, detector_apply]
    rw [(ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq S.val]
    ring
  change HasSum f value ↔ HasSum (aJointTerm s P Q R.val S.val d z) (A * value)
  refine (hasSum_mul_left_iff hA).symm.trans ?_
  constructor
  · intro h
    exact (hinj.hasSum_iff hoff).mp (h.congr_fun hterm)
  · intro h
    exact ((hinj.hasSum_iff hoff).mpr h).congr_fun fun E => (hterm E).symm

/-- Inversion exchanges the outer roots and keeps the separation ratio and
its relative principal lift. The lift equation implies the physical square
relation for the original roots. -/
theorem mixed_a_reversed_roots {d x z : ℂ} (hd : d ≠ 0) (hr : ‖d‖ < ‖z‖)
    (hLift : x = z * (1 + (d / z) ^ 2) ^ ((2 : ℂ)⁻¹)) :
    x ≠ 0 ∧ ‖(d / z) ^ 2‖ < 1 ∧ d / (x * z) ≠ 0 ∧ ‖d / (x * z)‖ < ‖x⁻¹‖ ∧
      (d / (x * z) / x⁻¹) ^ 2 = (d / z) ^ 2 ∧
      (d / (x * z)) ^ 2 = (z⁻¹) ^ 2 - (x⁻¹) ^ 2 ∧
      z⁻¹ = x⁻¹ * (1 + (d / (x * z) / x⁻¹) ^ 2) ^ ((2 : ℂ)⁻¹) := by
  have hzPos := (norm_nonneg d).trans_lt hr
  have hz := norm_pos_iff.mp hzPos
  have hdz : ‖d / z‖ < 1 := by rwa [norm_div, div_lt_one hzPos]
  have hρ : ‖(d / z) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hdz (by decide)
  let u : ℂ := 1 + (d / z) ^ 2
  let w : ℂ := u ^ ((2 : ℂ)⁻¹)
  have huRe : 0 < u.re := one_add_re_pos hρ
  have hu : u ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at huRe
    exact (lt_irrefl 0) huRe
  have hw : w ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hu)
  have hx : x ≠ 0 := hLift ▸ mul_ne_zero hz hw
  have hratio : d / (x * z) / x⁻¹ = d / z := by
    field_simp [hx, hz] <;> ring
  have hrad : ‖d / (x * z)‖ < ‖x⁻¹‖ := by
    have h : ‖d / (x * z) / x⁻¹‖ < 1 := hratio.symm ▸ hdz
    rwa [norm_div, div_lt_one (norm_pos_iff.mpr (inv_ne_zero hx))] at h
  have hwSq : w ^ 2 = u := by
    dsimp only [w]
    rw [pow_two, ← Complex.cpow_add _ _ hu,
      show (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 by norm_num, Complex.cpow_one]
  have hxSq : x ^ 2 = z ^ 2 + d ^ 2 := by
    calc
      x ^ 2 = z ^ 2 * u := by
        change x ^ 2 = z ^ 2 * u
        rw [show x = z * w from hLift, mul_pow, hwSq]
      _ = _ := by dsimp only [u]; field_simp [hz] <;> ring
  have hdSq : d ^ 2 = x ^ 2 - z ^ 2 := by rw [hxSq]; ring
  refine ⟨hx, hρ, div_ne_zero hd (mul_ne_zero hx hz), hrad,
    congrArg (fun a : ℂ => a ^ 2) hratio, ?_, ?_⟩
  · simp only [div_pow, mul_pow, inv_pow, hdSq]
    field_simp [hx, hz] <;> ring
  · rw [hratio]
    change z⁻¹ = x⁻¹ * w
    have hrel : w = x / z := (eq_div_iff hz).mpr (by rw [show x = z * w from hLift]; ring)
    rw [hrel]
    field_simp [hx, hz] <;> ring

private theorem reversed_prefactor (mP mQ mR mS : ℤ) (i j : ℕ)
    {d x z : ℂ} (hd : d ≠ 0) (hx : x ≠ 0) (hz : z ≠ 0) (hρ : ‖(d / z) ^ 2‖ < 1)
    (hLift : x = z * (1 + (d / z) ^ 2) ^ ((2 : ℂ)⁻¹)) :
    (x ^ (2 * (i : ℤ) - 2 * mP) * z ^ (2 * (j : ℤ) - 2 * mQ)) *
        aPrefactor (mQ - 2 * (j : ℤ)) (mP - 2 * (i : ℤ)) mS mR (d / (x * z)) x⁻¹ =
      aPrefactor mP mQ mR mS d z *
        ((((d / z) ^ 2) ^ (j + i)) * (1 + (d / z) ^ 2) ^ binomialExponent mP mQ mR mS j) := by
  let a := mP + mQ
  let b := mS - mR
  let l : ℤ := 2 * ((j + i : ℕ) : ℤ)
  let c := a - l
  let k := b - mP + mQ - 2 * (j : ℤ)
  let u : ℂ := 1 + (d / z) ^ 2
  let w : ℂ := u ^ ((2 : ℂ)⁻¹)
  have huRe : 0 < u.re := one_add_re_pos hρ
  have him : (Complex.log u * (2 : ℂ)⁻¹).im = u.arg / 2 := by
    rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.log_im]
    ring
  have harg := Complex.abs_arg_le_pi_div_two_iff.mpr huRe.le
  obtain ⟨hargLo, hargHi⟩ := abs_le.mp harg
  have hlo : -Real.pi < (Complex.log u * (2 : ℂ)⁻¹).im := by
    rw [him]
    linarith [Real.pi_pos]
  have hhi : (Complex.log u * (2 : ℂ)⁻¹).im ≤ Real.pi := by
    rw [him]
    linarith [Real.pi_pos]
  have hwPow : w ^ k = u ^ binomialExponent mP mQ mR mS j := by
    have he : (2 : ℂ)⁻¹ * (k : ℂ) = binomialExponent mP mQ mR mS j := by
      dsimp only [k, b, binomialExponent]
      push_cast
      ring
    rw [← he, Complex.cpow_mul _ hlo hhi, Complex.cpow_intCast]
  have hc : -((mQ - 2 * (j : ℤ)) + (mP - 2 * (i : ℤ))) = -c := by
    dsimp only [c, a, l]
    push_cast
    ring
  have hneg : mR - mS = -b := by dsimp only [b]; ring
  have hdPow : (d / (x * z)) ^ (-c) = d ^ (-c) * (x ^ c * z ^ c) := by
    rw [div_zpow, div_eq_mul_inv, ← zpow_neg, neg_neg, mul_zpow]
  have hxPow : (x⁻¹) ^ (-b) = x ^ b := by rw [inv_zpow', neg_neg]
  have hxExp : (2 * (i : ℤ) - 2 * mP) + c + b = k := by
    dsimp only [c, a, l, k]
    push_cast
    ring
  have hzExp : (2 * (j : ℤ) - 2 * mQ) + c = b - l - k := by
    dsimp only [c, a, l, k]
    ring
  dsimp only [aPrefactor]
  rw [hc, hneg, hdPow, hxPow, ratio_pow]
  change _ = (d ^ (-a) * z ^ b) * ((d ^ l * z ^ (-l)) * u ^ binomialExponent mP mQ mR mS j)
  rw [← hwPow]
  calc
    _ = d ^ (-c) * ((x ^ (2 * (i : ℤ) - 2 * mP) * x ^ c * x ^ b) *
        (z ^ (2 * (j : ℤ) - 2 * mQ) * z ^ c)) := by ring
    _ = d ^ (-c) * (x ^ k * z ^ (b - l - k)) := by
      rw [← zpow_add₀ hx (2 * (i : ℤ) - 2 * mP) c, ← zpow_add₀ hx,
        ← zpow_add₀ hz, hxExp, hzExp]
    _ = d ^ (-c) * (z ^ (b - l) * w ^ k) := by
      rw [show x = z * w from hLift, mul_zpow]
      calc
        _ = d ^ (-c) * ((z ^ k * z ^ (b - l - k)) * w ^ k) := by ring
        _ = _ := by rw [← zpow_add₀ hz, show k + (b - l - k) = b - l by ring]
    _ = _ := by
      rw [show -c = -a + l by dsimp only [c]; ring, zpow_add₀ hd,
        show b - l = b + -l by ring, zpow_add₀ hz]
      ring

/-- The actual mixed A double sum at the physical radial roots has the
detector-reversed value given by the reciprocal-root double sums. The phase,
factorials, and coordinate powers agree with the native B-product reversal. -/
theorem a_joint_iterate_hasSum_detector_reversal (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {d x z : ℂ} (hd : d ≠ 0) (hr : ‖d‖ < ‖z‖)
    (hLift : x = z * (1 + (d / z) ^ 2) ^ ((2 : ℂ)⁻¹)) :
    HasSum (aJointTerm s P Q R.val S.val d z)
      (Complex.I ^ ((M : ℤ) - K) * ∑ i ∈ Finset.range (M / 2 + 1),
        ∑ j ∈ Finset.range (K / 2 + 1),
          ((i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹ *
            (x ^ (2 * (i : ℤ) - 6 - 2 * (M : ℤ)) * z ^ (2 * (j : ℤ) - 6 - 2 * (K : ℤ)))) *
          ∑' p, aJointTerm (!s) ((T (!s) ^ j) Q) (swapInput ((T s ^ i) P))
            S.val (swapInput R).val (d / (x * z)) x⁻¹ p) := by
  obtain ⟨hx, hρ, hd', _, hratio, _, _⟩ := mixed_a_reversed_roots hd hr hLift
  have hz := norm_pos_iff.mp ((norm_nonneg d).trans_lt hr)
  have hsum := aCoeff_inversion_hasSum_unit_disk s t M K H J P Q R S hP hQ hR hS hρ
  have hphys := (aJoint_hasSum_iff_energy s t M K H J P Q R S hP hQ hR hS hd hz _).mp hsum
  refine Eq.mp (congrArg (fun v : ℂ => HasSum (aJointTerm s P Q R.val S.val d z) v) ?_) hphys
  let A := aPrefactor (weight M) (weight K) (weight H) (weight J) d z
  change A * (Complex.I ^ (weight M - weight K) * _) = _
  rw [show weight M - weight K = (M : ℤ) - K by dsimp only [weight]; ring,
    mul_left_comm A]
  apply congrArg (fun v : ℂ => Complex.I ^ ((M : ℤ) - K) * v)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hiM : 2 * i ≤ M := by have := Finset.mem_range.mp hi; omega
  have hjK : 2 * j ≤ K := by have := Finset.mem_range.mp hj; omega
  let Qj := (T (!s) ^ j) Q
  let Pi := swapInput ((T s ^ i) P)
  have hQj : Qj.val ∈ actualGrade ℒ leechUnit (K - 2 * j) := descend_grade hQ hjK
  have hPi : Pi.val ∈ actualGrade ℒ leechUnit (M - 2 * i) := swapped_grade (descend_grade hP hiM)
  have hR' : (swapInput R).val ∈ actualGrade ℒ leechUnit H := swapped_grade hR
  have shift_weight (G n : ℕ) (hn : 2 * n ≤ G) :
      weight (G - 2 * n) = weight G - 2 * (n : ℤ) := by
    dsimp only [weight]
    omega
  have hK := shift_weight K j hjK
  have hM := shift_weight M i hiM
  let V := ∑' E : ℕ, exchangedCoeff s t (weight M) (weight K) (weight H) (weight J)
    P Q R S j i E * ((d / z) ^ 2) ^ E
  have hDesc := (aCoeff_summable (!s) (!t) (K - 2 * j) (M - 2 * i) J H
    Qj Pi S (swapInput R) hQj hPi hS hR' hρ).hasSum
  have hDesc' : HasSum (fun E : ℕ => aCoeff (!s) (!t) (weight (K - 2 * j))
      (weight (M - 2 * i)) (weight J) (weight H) E Qj Pi S (swapInput R) *
        ((d / z) ^ 2) ^ E) V := by
    simpa only [V, exchangedCoeff, hK, hM, Qj, Pi] using hDesc
  have hBridge := aJoint_hasSum_iff_energy (!s) (!t) (K - 2 * j) (M - 2 * i) J H
    Qj Pi S (swapInput R) hQj hPi hS hR' hd' (inv_ne_zero hx) V
  rw [hratio] at hBridge
  have hTsum := (hBridge.mp hDesc').tsum_eq
  rw [show (∑' p, aJointTerm (!s) Qj Pi S.val (swapInput R).val (d / (x * z)) x⁻¹ p) =
    aPrefactor (weight (K - 2 * j)) (weight (M - 2 * i)) (weight J) (weight H)
      (d / (x * z)) x⁻¹ * V from hTsum, hK, hM]
  have hxExp : 2 * (i : ℤ) - 6 - 2 * (M : ℤ) = 2 * (i : ℤ) - 2 * weight M := by
    dsimp only [weight]
    ring
  have hzExp : 2 * (j : ℤ) - 6 - 2 * (K : ℤ) = 2 * (j : ℤ) - 2 * weight K := by
    dsimp only [weight]
    ring
  rw [hxExp, hzExp]
  let B := (((d / z) ^ 2) ^ (j + i)) *
    (1 + (d / z) ^ 2) ^ binomialExponent (weight M) (weight K) (weight H) (weight J) j
  change A * ((factorials i j)⁻¹ *
      ((((d / z) ^ 2) ^ (j + i)) *
        ((1 + (d / z) ^ 2) ^ binomialExponent (weight M) (weight K) (weight H) (weight J) j *
          V))) = _
  calc
    _ = (factorials i j)⁻¹ * ((A * B) * V) := by dsimp only [B]; ring
    _ = _ := by
      rw [← reversed_prefactor (weight M) (weight K) (weight H) (weight J) i j hd hx hz hρ hLift]
      simp only [factorials, mul_inv]
      ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalIterateInversion
