/- GID: D5/S3/Combinatorics/Circle/RadixFourNonunitZeroSubsets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/RadixFourNonunitZeroSubsets
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum, mathlib/module/Mathlib.Data.Nat.GCD.Basic]
   utility: none
   digest: Radix-four rotation positivity distinguishes nonunit physical zero fibres. -/

import D5.S3.Arith.Congruence.NonunitMultiplicationPeriod
import D5.S3.Arith.Congruence.PowerQuotientOrder
import D5.S3.Combinatorics.Circle.ZeroSumSubsets
import D5.S3.Combinatorics.Circle.TwoBitZeroSubsets
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Radix-four supported nonunit sources

All labels below are the actual full `Fin (2*n)` physical labels. Radix-four
rotation proves actual even-label positivity and the integral trace. Exact gcd
three then leaves only empty and full integer-zero subsets. The separation
conjunction includes both actual modular seed minimal periods via the generic
nonunit return bridge and the accepted quotient order. The centered doubleStep
period is a separate, unfinished bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace D5.S3.Combinatorics.Circle.RadixFourNonunitZeroSubsets

open SourceWidth ZeroSumSubsets
open scoped BigOperators

/-- The actual radix-four-supported natural seed, with digits indexed by `Fin n`. -/
def radixSeed {n : ℕ} (B : Finset (Fin n)) : ℕ := ∑ j ∈ B, 4 ^ j.val

/-- The actual even-label inclusion into the full physical source. -/
def evenLabel {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by omega⟩

/-- Physical even labels, as a subset of the complete label type. -/
def evenLabels (n : ℕ) : Finset (Fin (2 * n)) := Finset.univ.image evenLabel

private theorem evenLabel_injective (n : ℕ) :
    Function.Injective (@evenLabel n) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp [evenLabel] at this
  omega

private def digitSum (n : ℕ) : ℕ := ∑ j : Fin n, 4 ^ j.val

private theorem pow_four (n : ℕ) : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
  rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]

private theorem digitSum_three (n : ℕ) :
    3 * digitSum n = 2 ^ (2 * n) - 1 := by
  have h := geom_sum_mul_of_one_le (show 1 ≤ (4 : ℕ) by decide) n
  rw [Finset.sum_range] at h
  simpa only [digitSum, show (4 : ℕ) - 1 = 3 by decide,
    pow_four, Nat.mul_comm] using h

private theorem digitSum_pos {n : ℕ} (hn : 0 < n) : 0 < digitSum n := by
  have h := Finset.single_le_sum (f := fun j : Fin n => (4 : ℕ) ^ j.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  simpa only [Fin.val_mk, pow_zero, digitSum] using (lt_of_lt_of_le Nat.zero_lt_one h)

private theorem modulus_three (n : ℕ) :
    modulus (2 * n) = 3 * (digitSum n : ℤ) := by
  have hp : 1 ≤ (2 : ℕ) ^ (2 * n) := Nat.one_le_two_pow
  have h := congrArg (fun a : ℕ => (a : ℤ)) (digitSum_three n)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp,
    Nat.cast_pow, Nat.cast_one, modulus] using h.symm

private theorem modulus_odd {n : ℕ} (hn : 0 < n) : modulus (2 * n) % 2 = 1 := by
  have he : 2 * n = (2 * n - 1) + 1 := by omega
  rw [modulus, he, pow_succ]
  omega

private def rotatedValue {n : ℕ} (B : Finset (Fin n)) (i : Fin n) : ℕ :=
  ∑ j ∈ B, 4 ^ (finCycle i j).val

private theorem rotated_bounds {n : ℕ} (B : Finset (Fin n)) (hB : B.Nonempty)
    (i : Fin n) : 0 < rotatedValue B i ∧ rotatedValue B i ≤ digitSum n := by
  classical
  constructor
  · obtain ⟨j, hj⟩ := hB
    exact lt_of_lt_of_le (pow_pos (by decide : 0 < (4 : ℕ)) (finCycle i j).val)
      (Finset.single_le_sum (f := fun j : Fin n => (4 : ℕ) ^ (finCycle i j).val)
        (fun _ _ => Nat.zero_le _) hj)
  · have hperm : (∑ j : Fin n, 4 ^ (finCycle i j).val) = digitSum n :=
      Equiv.sum_comp (finCycle i) (fun j : Fin n => (4 : ℕ) ^ j.val)
    rw [← hperm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun _ _ _ => Nat.zero_le _)

private theorem power_rotation {n : ℕ} (i j : Fin n) :
    (4 : ℤ) ^ (finCycle i j).val ≡
      (4 : ℤ) ^ i.val * 4 ^ j.val [ZMOD modulus (2 * n)] := by
  have hi := i.isLt
  have hj := j.isLt
  rw [finCycle_apply, Fin.val_add]
  by_cases h : j.val + i.val < n
  · rw [Nat.mod_eq_of_lt h, pow_add, mul_comm (4 ^ j.val) (4 ^ i.val)]
  · have hmod : (j.val + i.val) % n = j.val + i.val - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    apply Int.modEq_iff_dvd.mpr
    refine ⟨(4 : ℤ) ^ (j.val + i.val - n), ?_⟩
    have hexp : i.val + j.val = (j.val + i.val - n) + n := by omega
    have hfour : (4 : ℤ) ^ n = (2 : ℤ) ^ (2 * n) := by
      exact_mod_cast pow_four n
    rw [← pow_add, hexp, pow_add, hfour, modulus]
    ring

private theorem rotated_residue {n : ℕ} (B : Finset (Fin n)) (i : Fin n) :
    (rotatedValue B i : ℤ) ≡
      (2 : ℤ) ^ (evenLabel i).val * (radixSeed B : ℤ)
        [ZMOD modulus (2 * n)] := by
  classical
  have hsum : (∑ j ∈ B, (4 : ℤ) ^ (finCycle i j).val) ≡
      ∑ j ∈ B, (4 : ℤ) ^ i.val * 4 ^ j.val [ZMOD modulus (2 * n)] := by
    induction B using Finset.induction_on with
    | empty => exact Int.ModEq.refl _
    | @insert j B hj ih =>
      simpa only [Finset.sum_insert hj] using (power_rotation i j).add ih
  have hp : (4 : ℤ) ^ i.val = (2 : ℤ) ^ (evenLabel i).val := by
    dsimp [evenLabel]
    exact_mod_cast pow_four i.val
  simpa only [rotatedValue, radixSeed, Nat.cast_sum, Nat.cast_pow,
    Nat.cast_ofNat, ← Finset.mul_sum, hp] using hsum

private theorem actual_even_eq_rotated {n : ℕ} (hn : 0 < n)
    (B : Finset (Fin n)) (hB : B.Nonempty) (i : Fin n) :
    actualSource (2 * n) (radixSeed B) (evenLabel i) = rotatedValue B i := by
  have hq := digitSum_pos hn
  obtain ⟨hlo, hhi⟩ := rotated_bounds B hB i
  have hN : 0 < modulus (2 * n) := by rw [modulus_three]; positivity
  have hbound : -(modulus (2 * n) / 2) ≤ (rotatedValue B i : ℤ) ∧
      (rotatedValue B i : ℤ) ≤ modulus (2 * n) / 2 := by
    have hqi : (0 : ℤ) < digitSum n := by exact_mod_cast hq
    have hloi : (0 : ℤ) < rotatedValue B i := by exact_mod_cast hlo
    have hhii : (rotatedValue B i : ℤ) ≤ digitSum n := by exact_mod_cast hhi
    rw [modulus_three]
    omega
  apply centered_unique hN (modulus_odd hn)
    (centered_bounds hN (modulus_odd hn) _) hbound
  rw [centered_mod]
  exact (rotated_residue B i).symm

/-- Every actual even physical label is strictly positive. No gcd or period
assumption is needed: multiplication by four rotates the actual 0/1 digits. -/
theorem actual_even_pos {n : ℕ} (hn : 0 < n) (B : Finset (Fin n))
    (hB : B.Nonempty) (i : Fin n) :
    0 < actualSource (2 * n) (radixSeed B) (evenLabel i) := by
  rw [actual_even_eq_rotated hn B hB i]
  exact_mod_cast (rotated_bounds B hB i).1

private theorem rotated_trace {n : ℕ} (B : Finset (Fin n)) :
    (∑ i : Fin n, rotatedValue B i) = B.card * digitSum n := by
  classical
  unfold rotatedValue
  rw [Finset.sum_comm]
  have hcol (j : Fin n) : (∑ i : Fin n, 4 ^ (finCycle i j).val) = digitSum n := by
    simpa only [finCycle_apply, add_comm, digitSum] using
      Equiv.sum_comp (finCycle j) (fun i : Fin n => (4 : ℕ) ^ i.val)
  simp_rw [hcol]
  simp

/-- Complete integral trace of all actual even labels. In particular the
positive even half has a nonzero sum; no rational or modular sum is substituted. -/
theorem actual_even_trace {n : ℕ} (hn : 0 < n) (B : Finset (Fin n))
    (hB : B.Nonempty) :
    3 * (∑ i : Fin n, actualSource (2 * n) (radixSeed B) (evenLabel i)) =
      (B.card : ℤ) * modulus (2 * n) := by
  simp_rw [actual_even_eq_rotated hn B hB]
  have h := congrArg (fun a : ℕ => (a : ℤ)) (rotated_trace B)
  simp only [Nat.cast_sum, Nat.cast_mul] at h
  rw [h, modulus_three]
  ring

private theorem mask_even (n : ℕ) : mask (evenLabels n) = digitSum n := by
  classical
  unfold evenLabels mask
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    exact (pow_four i.val).symm
  · exact fun _ _ _ _ he => evenLabel_injective n he

private theorem mask_odd (n : ℕ) : mask (evenLabels n)ᶜ = 2 * digitSum n := by
  classical
  have h := Finset.sum_add_sum_compl (evenLabels n)
    (fun i : Fin (2 * n) => (2 : ℕ) ^ i.val)
  change mask (evenLabels n) + mask (evenLabels n)ᶜ =
    mask (Finset.univ : Finset (Fin (2 * n))) at h
  rw [mask_even, mask_full] at h
  have hthree := digitSum_three n
  omega

private theorem even_sum_pos {n : ℕ} (hn : 0 < n)
    (B : Finset (Fin n)) (hB : B.Nonempty) :
    0 < ∑ p ∈ evenLabels n, actualSource (2 * n) (radixSeed B) p := by
  classical
  unfold evenLabels
  rw [Finset.sum_image]
  · exact Finset.sum_pos (fun i _ => actual_even_pos hn B hB i)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  · exact fun _ _ _ _ he => evenLabel_injective n he

private theorem zero_mask_cases {n t : ℕ} (hn : 0 < n)
    (hg : Nat.gcd t (2 ^ (2 * n) - 1) = 3)
    (A : Finset (Fin (2 * n)))
    (hz : (∑ p ∈ A, actualSource (2 * n) t p) = 0) :
    A = ∅ ∨ A = evenLabels n ∨ A = (evenLabels n)ᶜ ∨ A = Finset.univ := by
  have hq := digitSum_pos hn
  have hthree := digitSum_three n
  have hN : 0 < 2 ^ (2 * n) - 1 := by omega
  have hd := quotient_dvd hN (zero_mask_dvd A hz)
  rw [hg, ← hthree, Nat.mul_div_cancel_left _ (by decide : 0 < 3)] at hd
  obtain ⟨m, hm⟩ := hd
  have hb := mask_bound A
  have hm3 : m ≤ 3 := by
    by_contra h
    have hm4 : 4 ≤ m := by omega
    have hmul := Nat.mul_le_mul_left (digitSum n) hm4
    nlinarith
  have hmi : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hmi with rfl | rfl | rfl | rfl
  · left
    apply mask_injective (2 * n)
    simpa [mask] using hm
  · right; left
    apply mask_injective (2 * n)
    simpa [mask_even] using hm
  · right; right; left
    apply mask_injective (2 * n)
    simpa [mask_odd, Nat.mul_comm] using hm
  · right; right; right
    apply mask_injective (2 * n)
    rw [mask_full]
    nlinarith

/-- General physical indecomposability at exact gcd three. This quantifies over
every physical subset, including empty/full, for every positive n and nonempty B. -/
theorem actual_zero_iff {n : ℕ} (hn : 0 < n) (B : Finset (Fin n))
    (hB : B.Nonempty) (hg : Nat.gcd (radixSeed B) (2 ^ (2 * n) - 1) = 3)
    (A : Finset (Fin (2 * n))) :
    (∑ p ∈ A, actualSource (2 * n) (radixSeed B) p) = 0 ↔
      A = ∅ ∨ A = Finset.univ := by
  classical
  have htotal := (source_cycle (by omega : 0 < 2 * n) (radixSeed B)).2.1
  have heven := even_sum_pos hn B hB
  constructor
  · intro hz
    rcases zero_mask_cases hn hg A hz with h | h | h | h
    · exact Or.inl h
    · rw [h] at hz
      omega
    · have hc := Finset.sum_add_sum_compl (evenLabels n)
        (actualSource (2 * n) (radixSeed B))
      rw [htotal] at hc
      rw [h] at hz
      omega
    · exact Or.inr h
  · rintro (rfl | rfl)
    · simp
    · simpa using htotal

/-- The complete physical zero fibre has exactly two elements. -/
theorem actual_zero_subsets_card {n : ℕ} (hn : 0 < n) (B : Finset (Fin n))
    (hB : B.Nonempty) (hg : Nat.gcd (radixSeed B) (2 ^ (2 * n) - 1) = 3) :
    (Finset.univ.filter (fun A : Finset (Fin (2 * n)) =>
      (∑ p ∈ A, actualSource (2 * n) (radixSeed B) p) = 0)).card = 2 := by
  classical
  have he : (Finset.univ.filter (fun A : Finset (Fin (2 * n)) =>
      (∑ p ∈ A, actualSource (2 * n) (radixSeed B) p) = 0)) =
      {∅, Finset.univ} := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      actual_zero_iff hn B hB hg, Finset.mem_insert, Finset.mem_singleton]
  have hne : (∅ : Finset (Fin (2 * n))) ≠ Finset.univ := by
    intro h
    have : (⟨0, by omega⟩ : Fin (2 * n)) ∈ (∅ : Finset (Fin (2 * n))) := by
      rw [h]
      exact Finset.mem_univ _
    simpa using this
  rw [he]
  simp [hne]

private theorem gcd_three_seed (n : ℕ) : Nat.gcd 3 (2 ^ (2 * n) - 1) = 3 := by
  apply Nat.dvd_antisymm (Nat.gcd_dvd_left _ _)
  apply Nat.dvd_gcd (dvd_refl 3)
  rw [← digitSum_three n]
  exact dvd_mul_right _ _

/-- Exact arithmetic gcd for the three consecutive radix-four digits. The
divisible-by-three boundary is retained rather than silently excluded. -/
theorem seed21_gcd (n : ℕ) :
    Nat.gcd 21 (2 ^ (2 * n) - 1) = if 3 ∣ n then 21 else 3 := by
  have hpow : (2 : ℕ) ^ (2 * n) - 1 = 4 ^ n - 1 := by rw [pow_four]
  by_cases h3 : 3 ∣ n
  · rw [ite_eq_left h3]
    apply Nat.dvd_antisymm (Nat.gcd_dvd_left _ _)
    apply Nat.dvd_gcd (dvd_refl 21)
    have h63 : (4 : ℕ) ^ 3 - 1 ∣ 4 ^ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one 4 h3
    rw [hpow]
    exact (show 21 ∣ 4 ^ 3 - 1 by norm_num).trans h63
  · rw [ite_eq_right h3]
    have hcop : Nat.gcd 3 n = 1 :=
      (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr h3
    have hd63 : Nat.gcd 21 (2 ^ (2 * n) - 1) ∣ 4 ^ 3 - 1 :=
      (Nat.gcd_dvd_left _ _).trans (by norm_num : 21 ∣ 4 ^ 3 - 1)
    have hdN : Nat.gcd 21 (2 ^ (2 * n) - 1) ∣ 4 ^ n - 1 := by
      rw [← hpow]
      exact Nat.gcd_dvd_right _ _
    have hd := Nat.dvd_gcd hd63 hdN
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hcop] at hd
    apply Nat.dvd_antisymm (by simpa using hd)
    exact Nat.dvd_gcd (by decide) (by
      rw [← digitSum_three n]
      exact dvd_mul_right _ _)

private def firstThree (n : ℕ) (hn : 3 ≤ n) : Finset (Fin n) :=
  {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}

private theorem firstThree_seed (n : ℕ) (hn : 3 ≤ n) :
    radixSeed (firstThree n hn) = 21 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have he := congrArg (fun i : Fin n => i.val) h
    norm_num only [Fin.val_mk] at he
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro h
    have he := congrArg (fun i : Fin n => i.val) h
    norm_num only [Fin.val_mk] at he
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro h
    have he := congrArg (fun i : Fin n => i.val) h
    norm_num only [Fin.val_mk] at he
  norm_num [radixSeed, firstThree, h01, h02, h12]

/-- An infinite parameter family with the same exact gcd and actual modular seed
period, but different complete physical zero fibres. For instance n=3*k+4 supplies
infinitely many parameters. The original domain and all physical labels remain.
The periods consume the nonunit bridge and the existing power-quotient order. -/
theorem seed21_separation (n : ℕ) (hn : 3 ≤ n) (h3 : ¬3 ∣ n) :
    Nat.gcd 21 (2 ^ (2 * n) - 1) = 3 ∧
    Nat.gcd 3 (2 ^ (2 * n) - 1) = 3 ∧
    (∀ i : Fin n, 0 < actualSource (2 * n) 21 (evenLabel i)) ∧
    (∑ i : Fin n, actualSource (2 * n) 21 (evenLabel i)) =
      modulus (2 * n) ∧
    (∀ A : Finset (Fin (2 * n)),
      (∑ p ∈ A, actualSource (2 * n) 21 p) = 0 ↔ A = ∅ ∨ A = Finset.univ) ∧
    (Finset.univ.filter (fun A : Finset (Fin (2 * n)) =>
      (∑ p ∈ A, actualSource (2 * n) 21 p) = 0)).card = 2 ∧
    (Finset.univ.filter (fun A : Finset (Fin (2 * n)) =>
      (∑ p ∈ A, actualSource (2 * n) 3 p) = 0)).card = 4 ∧
    Function.minimalPeriod
      (fun x : ZMod (2 ^ (2 * n) - 1) => 2 * x) (3 : ZMod (2 ^ (2 * n) - 1)) =
      2 * n ∧
    Function.minimalPeriod
      (fun x : ZMod (2 ^ (2 * n) - 1) => 2 * x) (21 : ZMod (2 ^ (2 * n) - 1)) =
      2 * n := by
  classical
  let B := firstThree n hn
  have hB : B.Nonempty := by simp [B, firstThree]
  have hseed : radixSeed B = 21 := firstThree_seed n hn
  have hg : Nat.gcd 21 (2 ^ (2 * n) - 1) = 3 := by
    rw [seed21_gcd, ite_eq_right h3]
  have hgB : Nat.gcd (radixSeed B) (2 ^ (2 * n) - 1) = 3 := by rwa [hseed]
  have hcB : B.card = 3 := by
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h
      have he := congrArg (fun i : Fin n => i.val) h
      norm_num only [Fin.val_mk] at he
    have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      intro h
      have he := congrArg (fun i : Fin n => i.val) h
      norm_num only [Fin.val_mk] at he
    have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      intro h
      have he := congrArg (fun i : Fin n => i.val) h
      norm_num only [Fin.val_mk] at he
    simp [B, firstThree, h01, h02, h12]
  have hN : 0 < (2 : ℕ) ^ (2 * n) - 1 := by
    have hp := digitSum_pos (by omega : 0 < n)
    have he := digitSum_three n
    omega
  have horder : orderOf (2 : ZMod ((2 ^ (2 * n) - 1) / 3)) = 2 * n := by
    simpa [show n ≠ 1 by omega] using
      (D5.S3.Arith.Congruence.PowerQuotientOrder.power_quotient_order
        2 1 n (by omega) (by omega) (by omega))
  have hperiod (t : ℕ) (ht : Nat.gcd t (2 ^ (2 * n) - 1) = 3) :
      Function.minimalPeriod
        (fun x : ZMod (2 ^ (2 * n) - 1) => 2 * x) (t : ZMod (2 ^ (2 * n) - 1)) =
        2 * n := by
    have hp := D5.S3.Arith.Congruence.NonunitMultiplicationPeriod.minimalPeriod_mul_natCast
      (2 ^ (2 * n) - 1) 2 t hN
    rw [ht] at hp
    simpa only [Nat.cast_ofNat] using hp.trans horder
  refine ⟨hg, gcd_three_seed n, ?_, ?_, ?_, ?_, ?_,
    hperiod 3 (gcd_three_seed n), hperiod 21 hg⟩
  · intro i
    simpa only [hseed] using actual_even_pos (by omega) B hB i
  · have ht := actual_even_trace (by omega) B hB
    rw [hseed, hcB] at ht
    norm_num only [Nat.cast_ofNat] at ht
    linarith
  · intro A
    simpa only [hseed] using actual_zero_iff (by omega) B hB hgB A
  · simpa only [hseed] using actual_zero_subsets_card (by omega) B hB hgB
  · have ht := TwoBitZeroSubsets.actual_zero_subsets_card (2 * n) 1
      (by omega) (by omega) (by omega)
    have heven : Even (2 * n / Nat.gcd 1 (2 * n)) := by
      simpa using (show Even (2 * n) from ⟨n, by omega⟩)
    simpa [heven] using ht

/- The modular periods above do not identify TwoRunSource.period, whose state
is a centered integer under doubleStep. That interface still needs the return
iff for the two actual dynamics, centered representative uniqueness and the
integer/natural modulus cast bridge. The integer zero-fibre clauses above are
proved independently and retain the full Fin(2*n) labels. -/

end D5.S3.Combinatorics.Circle.RadixFourNonunitZeroSubsets
