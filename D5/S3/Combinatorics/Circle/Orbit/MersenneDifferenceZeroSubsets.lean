/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneDifferenceZeroSubsets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/MersenneDifferenceZeroSubsets
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate,
     mathlib/module/Mathlib.Data.Nat.GCD.Basic]
   utility: none
   digest: Binary powers classify and count physical Mersenne-difference zero subsets. -/
module

public import D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
import all D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
import all D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
public import Mathlib.Algebra.BigOperators.ModEq

/-! # Mersenne-difference seeds on all physical labels

Exact integer-zero subsets of the full physical source are rotation invariant;
the shared binary-mask count gives the complete gcd formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets

open SourceWidth ZeroSumSubsets
open scoped BigOperators

open private modulus_nat modulus_half pow_rotate_mod mask_image_cast mask_lt_of_ne_univ image_proper from D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
open D5.S3.Combinatorics.Circle.ZeroSumSubsets (divisible_mask_card)

/- The accepted one-step congruence already includes the wrap at the full
power period. Induction extends it to every exponent, including zero. -/
private theorem pow_rotate_mod_all {k : ℕ} (hk : 0 < k) (a : ℕ) (i : Fin k) :
    (2 : ℤ) ^ (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).val ≡
      (2 : ℤ) ^ a * 2 ^ i.val [ZMOD modulus k] := by
  by_cases hk1 : k = 1
  · subst k
    simp [Int.ModEq, modulus]
  have hk2 : 2 ≤ k := by omega
  induction a with
  | zero => simp
  | succ a ih =>
    have hs := pow_rotate_mod (a := 1) hk2 (by omega)
      (((finRotate k : Equiv.Perm (Fin k)) ^ a) i)
    simp only [pow_one] at hs
    have ht := hs.trans (ih.mul_left (2 : ℤ))
    simpa only [pow_one, pow_succ', Equiv.Perm.mul_apply, mul_assoc] using ht

/- This is the literal centered representative, with inclusive endpoint bounds.
It is more specific than the existing unsigned-potential source_cycle. -/
private theorem actual_difference {k : ℕ} (hk : 0 < k) (a : ℕ) (i : Fin k) :
    actualSource k (2 ^ a - 1) i =
      (2 : ℤ) ^ (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).val -
        (2 : ℤ) ^ i.val := by
  by_cases hk1 : k = 1
  · subst k
    simp [actualSource, modulus, centered]
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hN, hodd, hhalf⟩ := modulus_half hk2
  have hseed : ((2 ^ a - 1 : ℕ) : ℤ) = (2 : ℤ) ^ a - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow : 1 ≤ (2 : ℕ) ^ a)]
    norm_cast
  have hmod :
      (2 : ℤ) ^ (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).val - 2 ^ i.val ≡
        (2 : ℤ) ^ i.val * ((2 ^ a - 1 : ℕ) : ℤ) [ZMOD modulus k] := by
    calc
      _ ≡ (2 : ℤ) ^ a * 2 ^ i.val - 2 ^ i.val [ZMOD modulus k] :=
        (pow_rotate_mod_all hk a i).sub (Int.ModEq.refl _)
      _ = _ := by rw [hseed]; ring
  apply centered_unique hN hodd (centered_bounds hN hodd _) ?_ ?_
  · have hi := i.isLt
    have hj := (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).isLt
    have hpi : 0 < (2 : ℤ) ^ i.val := by positivity
    have hpj : 0 < (2 : ℤ) ^
        (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).val := by positivity
    have hbi : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (k - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hbj : (2 : ℤ) ^
        (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).val ≤ (2 : ℤ) ^ (k - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hhalf]
    constructor <;> omega
  · rw [centered_mod]
    exact hmod.symm

private theorem actual_sum_eq_mask_sub {k : ℕ} (hk : 0 < k) (a : ℕ)
    (A : Finset (Fin k)) :
    (∑ i ∈ A, actualSource k (2 ^ a - 1) i) =
      (mask (A.image ((finRotate k : Equiv.Perm (Fin k)) ^ a)) : ℤ) -
        (mask A : ℤ) := by
  classical
  calc
    _ = ∑ i ∈ A,
        ((2 : ℤ) ^ (((finRotate k : Equiv.Perm (Fin k)) ^ a) i).val -
          (2 : ℤ) ^ i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact actual_difference hk a i
    _ = _ := by
      rw [Finset.sum_sub_distrib, mask_image_cast]
      simp only [mask, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

/-- For every positive length and every exponent, exact integer zero on physical
labels is equivalent to invariance under the corresponding rotation. -/
theorem actual_zero_iff_rotation (k a : ℕ) (hk : 0 < k) (A : Finset (Fin k)) :
    (∑ i ∈ A, actualSource k (2 ^ a - 1) i) = 0 ↔
      A.image ((finRotate k : Equiv.Perm (Fin k)) ^ a) = A := by
  classical
  rw [actual_sum_eq_mask_sub hk a A]
  constructor
  · intro hz
    apply mask_injective k
    exact_mod_cast (sub_eq_zero.mp hz)
  · intro hA
    rw [hA, sub_self]

/- The reverse direction uses mask congruence and strict bounds only after
handling both physical endpoints. Thus modular zero is never silently
identified with integer zero. -/
private theorem actual_zero_iff_reduced_dvd (k a : ℕ) (hk : 0 < k)
    (A : Finset (Fin k)) :
    (∑ i ∈ A, actualSource k (2 ^ a - 1) i) = 0 ↔
      (2 ^ k - 1) / Nat.gcd (2 ^ a - 1) (2 ^ k - 1) ∣ mask A := by
  classical
  have hN : 0 < 2 ^ k - 1 := by
    have hp := Nat.one_lt_two_pow (ne_of_gt hk)
    omega
  constructor
  · intro hz
    exact quotient_dvd hN (zero_mask_dvd A hz)
  · intro hd
    by_cases he : A = ∅
    · subst A
      simp
    by_cases hu : A = Finset.univ
    · subst A
      simpa using (source_cycle hk (2 ^ a - 1)).2.1
    let g := Nat.gcd (2 ^ a - 1) (2 ^ k - 1)
    change (2 ^ k - 1) / g ∣ mask A at hd
    have hgN : g ∣ 2 ^ k - 1 := Nat.gcd_dvd_right _ _
    have hgt : g ∣ 2 ^ a - 1 := Nat.gcd_dvd_left _ _
    obtain ⟨m, hm⟩ := hd
    obtain ⟨q, hq⟩ := hgt
    have hmul : g * ((2 ^ k - 1) / g) = 2 ^ k - 1 :=
      Nat.mul_div_cancel' hgN
    have hd' : (2 ^ k - 1) ∣ (2 ^ a - 1) * mask A := by
      refine ⟨q * m, ?_⟩
      rw [hm, hq]
      calc
        g * q * ((2 ^ k - 1) / g * m) =
            (g * ((2 ^ k - 1) / g)) * (q * m) := by ring
        _ = _ := by rw [hmul]
    have hdI : modulus k ∣ ((2 ^ a - 1 : ℕ) : ℤ) * (mask A : ℤ) := by
      rw [modulus_nat]
      exact_mod_cast hd'
    have hseed : ((2 ^ a - 1 : ℕ) : ℤ) = (2 : ℤ) ^ a - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow : 1 ≤ (2 : ℕ) ^ a)]
      norm_cast
    have hmcong : (mask A : ℤ) ≡
        (2 : ℤ) ^ a * (mask A : ℤ) [ZMOD modulus k] := by
      apply Int.modEq_iff_dvd.mpr
      simpa only [hseed, sub_mul, one_mul] using hdI
    have hrot :
        (mask (A.image ((finRotate k : Equiv.Perm (Fin k)) ^ a)) : ℤ) ≡
          (2 : ℤ) ^ a * (mask A : ℤ) [ZMOD modulus k] := by
      rw [mask_image_cast]
      simpa only [mask, Nat.cast_sum, Nat.cast_pow,
        Nat.cast_ofNat, Finset.mul_sum] using
        (Int.ModEq.sum (s := A) (fun i _ => pow_rotate_mod_all hk a i))
    have hcong := hrot.trans hmcong.symm
    rw [modulus_nat] at hcong
    have hnat :
        mask (A.image ((finRotate k : Equiv.Perm (Fin k)) ^ a)) ≡
          mask A [MOD 2 ^ k - 1] := Int.natCast_modEq_iff.mp hcong
    apply (actual_zero_iff_rotation k a hk A).mpr
    apply mask_injective k
    exact hnat.eq_of_lt_of_lt
      (mask_lt_of_ne_univ _ (image_proper _ A hu))
      (mask_lt_of_ne_univ A hu)

/-- The full physical zero fibre has exactly `2 ^ gcd a k` subsets. Repeated
source values do not identify labels, and no restriction on `a` is imposed. -/
theorem actual_zero_subsets_card (k a : ℕ) (hk : 0 < k) :
    (Finset.univ.filter (fun A : Finset (Fin k) =>
      (∑ i ∈ A, actualSource k (2 ^ a - 1) i) = 0)).card =
        2 ^ Nat.gcd a k := by
  classical
  simp_rw [actual_zero_iff_reduced_dvd k a hk]
  rw [divisible_mask_card k (2 ^ a - 1) hk,
    Nat.pow_sub_one_gcd_pow_sub_one,
    Nat.sub_add_cancel (Nat.one_le_two_pow : 1 ≤ (2 : ℕ) ^ Nat.gcd a k)]

end D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets
