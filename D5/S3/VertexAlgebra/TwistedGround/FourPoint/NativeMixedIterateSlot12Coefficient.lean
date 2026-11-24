/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedIterateSlot12Coefficient
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite upper half-turn exchange of actual native Leech A coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm

/-! Exchange of the first two mixed insertions at one native A energy. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Coefficient

open ActualLeechHyperbolic (leechData)
open ActualEnergyRestrictedDual (maxOddWeight)
open Complex (I)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeSugawaraConformal (translation)
open Orbifold.NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit oddTranslation)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeMixedPairSkew (swapInput mu_skew_of_grade mu_skew_translation_tail)
open Orbifold.NativeDetectorTranslation (detector selected_detector_divided_translation)
open Orbifold.NativeMixedIterateInversionCoefficient (aCoeff)
open private odd_translation_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
open private maxOddWeight_le_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm

local notation "ℒ" => leechData
local notation "U" => oddTranslation ℒ
local notation "B" => detector ℒ leechUnit

private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev weight (M : ℕ) : ℤ := 3 + (M : ℤ)

set_option maxHeartbeats 1000000 in
-- Elaborate the finite detector exchange on the native twisted spaces.
/-- Upper half-turn exchange of the mixed pair. The detector inputs stay in
their original order, and divided translation lowers the selected detector mode
from energy `E - h` to the mode selected at energy `E`. -/
theorem aCoeff_slot12_exchange (s t : Bool) (M K : ℕ) (mR mS : ℤ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t)) (E : ℕ)
    (hP : P.val ∈ actualGrade ℒ leechUnit M)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    aCoeff s t (weight M) (weight K) mR mS E P Q R S =
      (-1 : ℂ) ^ (3 + M) * ∑ h ∈ Finset.range (E + 1),
        I ^ (2 * ((E - h : ℕ) : ℤ) - weight M - weight K) *
          Ring.choose (((mS : ℂ) - (mR : ℂ)) / 2 - ((E - h : ℕ) : ℂ)) h *
          aCoeff (!s) t (weight K) (weight M) mR mS (E - h) Q (swapInput (s := s) P) R S := by
  classical
  let e : ℤ := 2 * (E : ℤ) - weight M - weight K
  let q : ℤ := mS - mR - 2 * (E : ℤ)
  let source (h : ℕ) : OddCarrier ℒ :=
    (mu (!s) Q).coeff (e - 2 * (h : ℤ)) (swapInput (s := s) P)
  let term (h : ℕ) : OddCarrier ℒ :=
    (I ^ (e - 2 * (h : ℤ)) * (h.factorial : ℂ)⁻¹) • (U ^ h) (source h)
  have hPmax : (maxOddWeight ℒ leechUnit P.val : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast maxOddWeight_le_grade hP
  have hQmax : (maxOddWeight ℒ leechUnit Q.val : ℤ) ≤ (K : ℤ) := by
    exact_mod_cast maxOddWeight_le_grade hQ
  have hsupport : Function.support term ⊆ (Finset.range (E + 1) : Set ℕ) := by
    intro h hh
    apply Finset.mem_range.mpr
    by_contra hout
    apply hh
    have hEhNat : E ≤ h := (Nat.le_succ E).trans (Nat.le_of_not_gt hout)
    have hEh : (E : ℤ) ≤ (h : ℤ) := by exact_mod_cast hEhNat
    have htailBound :
        e + (maxOddWeight ℒ leechUnit P.val : ℤ) + maxOddWeight ℒ leechUnit Q.val + 6 ≤
          2 * (h : ℤ) := by
      dsimp only [e, weight]
      linarith only [hPmax, hQmax, hEh]
    dsimp only [term, source]
    rw [mu_skew_translation_tail s e P Q h htailBound, smul_zero]
  have hskew :
      (mu s P).coeff e Q = (-1 : ℂ) ^ (3 + M) • ∑ h ∈ Finset.range (E + 1), term h := by
    have skew := mu_skew_of_grade true s M K e P Q hP hQ
    change (mu s P).coeff e Q = (-1 : ℂ) ^ (3 + M) • ∑ᶠ h, term h at skew
    rw [skew, finsum_eq_sum_of_support_subset term hsupport]
  have hdet := congrArg (fun a : OddCarrier ℒ => B q R.val S.val a.val) hskew
  simp only [term, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul,
    odd_translation_pow_val, mul_assoc] at hdet
  change B q R.val S.val ((mu s P).coeff e Q).val = _
  rw [hdet]
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (3 + M) * z)
  apply Finset.sum_congr rfl
  intro h hh
  have hhE : h ≤ E := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  have hFE : ((E - h : ℕ) : ℤ) + (h : ℤ) = (E : ℤ) := by
    rw [Nat.cast_sub hhE, sub_add_cancel]
  have hp : e - 2 * (h : ℤ) = 2 * ((E - h : ℕ) : ℤ) - weight M - weight K := by
    dsimp only [e, weight]
    linarith only [hFE]
  have hsource :
      source h = (mu (!s) Q).coeff
        (2 * ((E - h : ℕ) : ℤ) - weight K - weight M) (swapInput (s := s) P) := by
    have hp' : e - 2 * (h : ℤ) = 2 * ((E - h : ℕ) : ℤ) - weight K - weight M := by
      rw [hp]
      ring
    simp only [source, hp']
  have ht := selected_detector_divided_translation ℒ leechUnit mR mS
    ((E - h : ℕ) : ℤ) R.val S.val (source h).val h
  rw [hFE] at ht
  change I ^ (e - 2 * (h : ℤ)) *
      ((h.factorial : ℂ)⁻¹ * B (mS - mR - 2 * (E : ℤ)) R.val S.val
        ((translation ℒ ^ h) (source h).val)) = _
  rw [ht]
  simp only [hp, hsource, aCoeff, Int.cast_natCast, mul_assoc]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Coefficient
