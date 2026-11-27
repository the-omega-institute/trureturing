/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddRightDetectorTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddRightDetectorTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divided source translation through the actual odd right field. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWard
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import Mathlib.RingTheory.Binomial

/-! Source translation under the actual upper odd right field in the doubled
Hahn coordinate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddRightDetectorTranslation

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open ActualChargedAdjoint (actualForm)
open NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit oddTranslation J)
open NativeOddUpperRightSkew
  (rightField rightField_coeff rightField_even_zero R_pairing_finite
    lowering mixedPairing_lowering_tail)
open LatticeHalfFockOriginalTranslation (correctedField_translation_physical)
open private J_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private lowering_grade lowering_small from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWard

private abbrev State (s : Bool) := Twisted leechData leechUnit s
private abbrev Odd := OddCarrier leechData

local notation "U" => oddTranslation leechData
local notation "L" => lowering leechData leechUnit
local notation "B" => actualForm leechData leechUnit

private abbrev invFact (k : ℕ) : ℂ := (k.factorial : ℂ)⁻¹

/-- The original twisted pairing against one signed coefficient of the upper
odd right field. -/
def detector (s : Bool) (e : ℤ) (P : State s) (S : State (!s)) (a : Odd) : ℂ :=
  B S.val ((rightField leechData leechUnit s P).coeff e a).val

private theorem detector_zero (s : Bool) (e : ℤ) (P : State s) (a : Odd) :
    detector s e P 0 a = 0 := by
  simp [detector]

private def term (s : Bool) (n : ℤ) (P : State s) (S : State (!s))
    (a : Odd) (k : ℕ) : ℂ :=
  (Complex.I ^ (-2 * (n + (k : ℤ)) - 3) * invFact k) *
    B ((L (!s) ^ k) S).val (J leechData leechUnit s (n + (k : ℤ)) a P).val

private theorem detector_mode (s : Bool) (n : ℤ) (N : ℕ) (P : State s)
    (S : State (!s)) (a : Odd) (hS : S.val ∈ actualGrade leechData leechUnit N) :
    detector s (-2*n-3) P S a =
      ∑ k ∈ Finset.range (N/2+1), term s n P S a k := by
  rw [detector, rightField_coeff, R_pairing_finite leechData leechUnit s n N P a S hS]
  apply Finset.sum_congr rfl
  intro k _
  rw [term, lowering_pow_val]

private theorem detector_lowering_mode (s : Bool) (n : ℤ) (N : ℕ) (P : State s)
    (S : State (!s)) (a : Odd) (hS : S.val ∈ actualGrade leechData leechUnit N) :
    detector s (-2*n-3) P (L (!s) S) a =
      ∑ k ∈ Finset.range (N/2), term s n P (L (!s) S) a k := by
  by_cases hN : 2 ≤ N
  · rw [detector_mode s n (N-2) P _ a (lowering_grade (!s) N S hS hN),
      show (N-2)/2+1 = N/2 by omega]
  · rw [lowering_small (!s) N S hS (by omega), detector_zero, show N/2 = 0 by omega]
    simp

private theorem invFact_succ (k : ℕ) :
    ((k+1 : ℕ) : ℂ) * invFact (k+1) = invFact k := by
  have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  change ((k+1 : ℕ) : ℂ) * (((k+1).factorial : ℂ)⁻¹) = (k.factorial : ℂ)⁻¹
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  calc
    _ = (((k+1 : ℕ) : ℂ) * (((k+1 : ℕ) : ℂ)⁻¹)) * invFact k := by ring
    _ = _ := by rw [mul_inv_cancel₀ hk, one_mul]

private theorem term_source_translation (s : Bool) (n : ℤ) (P : State s)
    (S : State (!s)) (a : Odd) (k : ℕ) :
    term s n P S (U a) k =
      ((k : ℂ) - (((-2*n-3+2 : ℤ) : ℂ) / 2)) * term s (n-1) P S a k := by
  have he : -2*(n-1+(k : ℤ))-3 = -2*(n+(k : ℤ))-3+2 := by omega
  have hc : (((-2*(n+(k : ℤ))-3+2 : ℤ) : ℂ) / 2) =
      (((-2*n-3+2 : ℤ) : ℂ) / 2) - (k : ℂ) := by
    push_cast
    ring
  have hI : Complex.I ^ (-2*(n+(k : ℤ))-3) =
      -Complex.I ^ (-2*(n-1+(k : ℤ))-3) := by
    have hI₂ : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq]
    rw [he, zpow_add₀ Complex.I_ne_zero, hI₂, mul_neg_one, neg_neg]
  have hJ : (J leechData leechUnit s (n+(k : ℤ)) (U a) P).val =
      ((((-2*n-3+2 : ℤ) : ℂ) / 2) - (k : ℂ)) •
        (J leechData leechUnit s (n-1+(k : ℤ)) a P).val := by
    rw [J_val, show (U a).val = LatticeSugawaraConformal.translation leechData a.val
      from rfl, correctedField_translation_physical, hc, ← he, J_val]
  simp only [term, hJ, hI, map_smul, smul_eq_mul]
  ring

private theorem term_lowering (s : Bool) (n : ℤ) (P : State s)
    (S : State (!s)) (a : Odd) (k : ℕ) :
    term s n P (L (!s) S) a k =
      ((k+1 : ℕ) : ℂ) * term s (n-1) P S a (k+1) := by
  have hn : n-1+((k+1 : ℕ) : ℤ) = n+(k : ℤ) := by omega
  simp only [term, hn, pow_succ (L (!s)) k, Module.End.mul_apply]
  rw [← invFact_succ k]
  ring

/-- The source translation of the actual upper odd right coefficient is
detector lowering minus the physical derivative of the upper right field.
The signed doubled exponent may be positive, negative or zero. -/
theorem detector_source_translation (s : Bool) (e : ℤ) (N : ℕ) (P : State s)
    (S : State (!s)) (a : Odd) (hS : S.val ∈ actualGrade leechData leechUnit N) :
    detector s e P S (U a) =
      detector s e P (L (!s) S) a -
        (((e+2 : ℤ) : ℂ) / 2) * detector s (e+2) P S a := by
  by_cases hEven : Even e
  · have hEven' : Even (e+2) := hEven.add (show Even (2 : ℤ) from ⟨1, by decide⟩)
    simp [detector, rightField_even_zero leechData leechUnit s e hEven,
      rightField_even_zero leechData leechUnit s (e+2) hEven']
  · obtain ⟨b, hb⟩ := Int.not_even_iff_odd.mp hEven
    let n := -b-2
    have he : e = -2*n-3 := by dsimp [n]; omega
    have shifted : detector s (-2*n-3+2) P S a =
        ∑ k ∈ Finset.range (N/2+1), term s (n-1) P S a k := by
      rw [show -2*n-3+2 = -2*(n-1)-3 by omega, detector_mode s (n-1) N P S a hS]
    rw [he, detector_mode s n N P S (U a) hS, detector_lowering_mode s n N P S a hS, shifted]
    let f := term s (n-1) P S a
    let x : ℂ := (((-2*n-3+2 : ℤ) : ℂ) / 2)
    have shift : (∑ k ∈ Finset.range (N/2+1), (k : ℂ) * f k) =
        ∑ k ∈ Finset.range (N/2), term s n P (L (!s) S) a k := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact Finset.sum_congr rfl (fun k _ => (term_lowering s n P S a k).symm)
    calc
      _ = ∑ k ∈ Finset.range (N/2+1), ((k : ℂ) - x) * f k :=
        Finset.sum_congr rfl (fun k _ => term_source_translation s n P S a k)
      _ = (∑ k ∈ Finset.range (N/2+1), (k : ℂ) * f k) -
            x * ∑ k ∈ Finset.range (N/2+1), f k := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [shift]

private theorem choose_succ (x : ℂ) (q : ℕ) :
    x * Ring.choose (x-1) q = ((q+1 : ℕ) : ℂ) * Ring.choose x (q+1) := by
  simpa only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_one, Nat.add_sub_cancel,
    Ring.choose_one_right] using
    (Ring.choose_smul_choose x (n := q+1) (k := 1) (by omega)).symm

private def dividedWeight (x : ℂ) (h j : ℕ) : ℂ :=
  invFact j * Ring.choose x (h-j)

private theorem divided_sum_succ (x : ℂ) (h : ℕ) (F : ℕ → ℂ) :
    (∑ j ∈ Finset.range (h+1), dividedWeight x h j * F (j+1)) +
        x * (∑ j ∈ Finset.range (h+1), dividedWeight (x-1) h j * F j) =
      ((h+1 : ℕ) : ℂ) * ∑ j ∈ Finset.range (h+2), dividedWeight x (h+1) j * F j := by
  let g (j : ℕ) := (j : ℂ) * dividedWeight x (h+1) j * F j
  let f (j : ℕ) := ((h+1-j : ℕ) : ℂ) * dividedWeight x (h+1) j * F j
  have hg : (∑ j ∈ Finset.range (h+1), dividedWeight x h j * F (j+1)) =
      ∑ j ∈ Finset.range (h+2), g j := by
    rw [Finset.sum_range_succ' g (h+1), show g 0 = 0 by simp [g], add_zero]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g, dividedWeight]
    rw [show h+1-(j+1) = h-j by omega, ← mul_assoc _ (invFact (j+1)) _,
      invFact_succ]
  have hf : x * (∑ j ∈ Finset.range (h+1), dividedWeight (x-1) h j * F j) =
      ∑ j ∈ Finset.range (h+2), f j := by
    rw [Finset.mul_sum, Finset.sum_range_succ f (h+1), show f (h+1) = 0 by simp [f],
      add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hjh : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    dsimp only [f, dividedWeight]
    rw [show h+1-j = (h-j)+1 by omega]
    calc
      _ = invFact j * (x * Ring.choose (x-1) (h-j)) * F j := by ring
      _ = _ := by rw [choose_succ]; ring
  rw [hg, hf, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjh : j ≤ h+1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  dsimp only [g, f]
  rw [Nat.cast_sub hjh]
  ring

private theorem detector_divided_full (s : Bool) (h : ℕ) (e : ℤ) (N : ℕ)
    (P : State s) (S : State (!s)) (a : Odd) (hS : S.val ∈ actualGrade leechData leechUnit N) :
    invFact h * detector s e P S ((U ^ h) a) =
      ∑ j ∈ Finset.range (h+1), dividedWeight (-(e : ℂ)/2-1) h j *
        detector s (e+2*((h-j : ℕ) : ℤ)) P ((L (!s) ^ j) S) a := by
  induction h generalizing e N S with
  | zero => simp [dividedWeight]
  | succ h ih =>
    let x : ℂ := -(e : ℂ)/2-1
    let F (j : ℕ) := detector s (e+2*((h+1-j : ℕ) : ℤ)) P ((L (!s) ^ j) S) a
    have hx : -((e+2 : ℤ) : ℂ)/2-1 = x-1 := by
      dsimp only [x]
      push_cast
      ring
    have hx' : -(((e+2 : ℤ) : ℂ)/2) = x := by
      dsimp only [x]
      push_cast
      ring
    have hlower : invFact h * detector s e P (L (!s) S) ((U ^ h) a) =
        ∑ j ∈ Finset.range (h+1), dividedWeight x h j * F (j+1) := by
      by_cases hN : 2 ≤ N
      · rw [ih e (N-2) (L (!s) S) (lowering_grade (!s) N S hS hN)]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [F, x]
        rw [show h+1-(j+1) = h-j by omega, pow_succ (L (!s)) j, Module.End.mul_apply]
      · simp only [F, pow_succ (L (!s)), Module.End.mul_apply,
          lowering_small (!s) N S hS (by omega), map_zero, detector_zero, mul_zero,
          Finset.sum_const_zero]
    have hshift : invFact h * detector s (e+2) P S ((U ^ h) a) =
        ∑ j ∈ Finset.range (h+1), dividedWeight (x-1) h j * F j := by
      rw [ih (e+2) N S hS, hx]
      apply Finset.sum_congr rfl
      intro j hj
      have hjh : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have he : e+2+2*((h-j : ℕ) : ℤ) = e+2*((h+1-j : ℕ) : ℤ) := by omega
      rw [he]
    apply mul_left_cancel₀ (show ((h+1 : ℕ) : ℂ) ≠ 0 by
      exact_mod_cast Nat.succ_ne_zero h)
    change ((h+1 : ℕ) : ℂ) * (invFact (h+1) * detector s e P S ((U ^ (h+1)) a)) =
      ((h+1 : ℕ) : ℂ) * ∑ j ∈ Finset.range (h+2), dividedWeight x (h+1) j * F j
    rw [← mul_assoc, invFact_succ, pow_succ' U, Module.End.mul_apply,
      detector_source_translation s e N P S ((U ^ h) a) hS, sub_eq_add_neg,
      ← neg_mul, hx', mul_add, mul_left_comm (invFact h) x, hlower, hshift]
    exact divided_sum_succ x h F

/-- Divided source translation with the detector descendants truncated at
their actual grade. In doubled coordinates the shift of order `h-j` has
binomial upper argument `-e/2-1` for every signed exponent `e`. -/
theorem detector_divided_source_translation (s : Bool) (h : ℕ) (e : ℤ) (N : ℕ)
    (P : State s) (S : State (!s)) (a : Odd) (hS : S.val ∈ actualGrade leechData leechUnit N) :
    (h.factorial : ℂ)⁻¹ * detector s e P S ((U ^ h) a) =
      ∑ j ∈ Finset.range (min h (N/2)+1),
        ((j.factorial : ℂ)⁻¹ * Ring.choose (-(e : ℂ)/2-1) (h-j)) *
          detector s (e+2*((h-j : ℕ) : ℤ)) P ((L (!s) ^ j) S) a := by
  rw [detector_divided_full s h e N P S a hS]
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ (min_le_left _ _))
  · intro j hj hj'
    have hjh : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjN : N/2+1 ≤ j := by
      have hmin : min h (N/2)+1 ≤ j :=
        Nat.le_of_not_gt (fun hlt => hj' (Finset.mem_range.mpr hlt))
      by_cases hle : h ≤ N/2
      · rw [min_eq_left hle] at hmin
        omega
      · rwa [min_eq_right (by omega : N/2 ≤ h)] at hmin
    rw [mixedPairing_lowering_tail (!s) N S hS j hjN, detector_zero, mul_zero]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddRightDetectorTranslation
