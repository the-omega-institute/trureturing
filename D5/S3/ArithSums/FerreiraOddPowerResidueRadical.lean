/- GID: D5/S3/ArithSums/FerreiraOddPowerResidueRadical
   generality: I
   mirror-B: D5/B/S3/ArithSums/FerreiraOddPowerResidueRadical
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.RingTheory.Radical.NatInt, mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: The literal odd-power residue sum has positive rational deficit and recovers the radical of its odd modulus. -/

import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.FerreiraOddPowerResidueRadical

open scoped BigOperators

/-- The literal sequence definition in OEIS A399232. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (4 * n + 2), k ^ (4 * n + 1) % (2 * n + 1)

/-- The signed rational deficit is positive and its quotient recovers the radical. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    0 < ((2 * n + 1 : ℕ) : ℚ) ^ 2 - (a n : ℚ) ∧
    ((UniqueFactorizationMonoid.radical (2 * n + 1 : ℕ) : ℕ) : ℚ) =
      ((2 * n + 1 : ℕ) : ℚ) ^ 2 /
        (((2 * n + 1 : ℕ) : ℚ) ^ 2 - (a n : ℚ)) := by
  classical
  let m := 2 * n + 1
  let e := 4 * n + 1
  let r := UniqueFactorizationMonoid.radical m
  let q := m / r
  let f : ℕ → ℕ := fun x => x ^ e % m
  let B := Finset.Ioc 0 m
  have hm : 0 < m := by dsimp [m]; omega
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  let : NeZero m := ⟨hm0⟩
  have he : m ≤ e := by dsimp [m, e]; omega
  have ho : Odd e := ⟨2 * n, by dsimp [e]; omega⟩
  have hr : 0 < r := Nat.radical_pos m
  have hrd : r ∣ m := UniqueFactorizationMonoid.radical_dvd_self
  have hrq : r * q = m := Nat.mul_div_cancel' hrd
  have hq : 0 < q := by nlinarith
  have hz (x : ℕ) : m ∣ x ^ e ↔ r ∣ x := by
    constructor
    · intro h
      exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hm0).mp ⟨e, h⟩
    · intro h
      exact (Nat.dvd_radical_pow_self hm0).trans
        (pow_dvd_pow_of_dvd_of_le h he)
  have hfv (x : ℕ) : ((x : ZMod m) ^ e).val = f x := by
    rw [← Nat.cast_pow, ZMod.val_natCast]
  have hmc : (m : ZMod m) = 0 := by simp
  have hp (x : ℕ) : f (x + m) = f x := by
    rw [← hfv, ← hfv, Nat.cast_add, hmc, add_zero]
  have hblock : (∑ x ∈ Finset.Ioc m (m + m), f x) = ∑ x ∈ B, f x := by
    symm
    apply Finset.sum_nbij' (fun x => x + m) (fun x => x - m)
    · intro x hx
      simp only [B, Finset.mem_Ioc] at hx ⊢
      omega
    · intro x hx
      simp only [B, Finset.mem_Ioc] at hx ⊢
      omega
    · intro x hx
      omega
    · intro x hx
      simp only [Finset.mem_Ioc] at hx
      omega
    · intro x hx
      exact (hp x).symm
  have hablock : a n = (∑ x ∈ B, f x) + ∑ x ∈ B, f x := by
    have hi : Finset.Icc 1 (4 * n + 2) = Finset.Ioc 0 (m + m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      dsimp [m]
      omega
    change (∑ x ∈ Finset.Icc 1 (4 * n + 2), f x) = _
    rw [hi, ← Finset.sum_Ioc_consecutive f (Nat.zero_le m) (by omega), hblock]
  let t : ℕ → ℕ := fun x => if x = m then m else m - x
  have htmem (x : ℕ) (hx : x ∈ B) : t x ∈ B := by
    simp only [B, Finset.mem_Ioc] at hx ⊢
    dsimp [t]
    split_ifs <;> omega
  have htt (x : ℕ) (hx : x ∈ B) : t (t x) = x := by
    simp only [B, Finset.mem_Ioc] at hx
    dsimp [t]
    split_ifs <;> omega
  have htcast (x : ℕ) (hx : x ∈ B) : (t x : ZMod m) = -(x : ZMod m) := by
    have hle : x ≤ m := (Finset.mem_Ioc.mp hx).2
    dsimp [t]
    split_ifs with h
    · subst x
      simp
    · rw [Nat.cast_sub hle, hmc, zero_sub]
  have hpair (x : ℕ) (hx : x ∈ B) :
      f x + f (t x) + (if r ∣ x then m else 0) = m := by
    have hzz : (x : ZMod m) ^ e = 0 ↔ r ∣ x := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact hz x
    have hv : f x < m := by
      rw [← hfv]
      exact ZMod.val_lt _
    have hft : f (t x) = if r ∣ x then 0 else m - f x := by
      rw [← hfv, htcast x hx, ho.neg_pow, ZMod.neg_val, hfv]
      simp only [hzz]
    by_cases h : r ∣ x
    · have hfx : f x = 0 := by rw [← hfv, hzz.mpr h]; rfl
      simp [hft, h, hfx]
    · rw [hft, if_neg h, if_neg h]
      omega
  have htsum : (∑ x ∈ B, f (t x)) = ∑ x ∈ B, f x := by
    exact Finset.sum_nbij' t t htmem htmem htt htt (fun _ _ => rfl)
  have hcount : (B.filter fun x => r ∣ x).card = q :=
    Nat.Ioc_filter_dvd_card_eq_div m r
  have hzero : (∑ x ∈ B, if r ∣ x then m else 0) = q * m := by
    rw [← Finset.sum_filter]
    simp [hcount]
  have hsum : (∑ x ∈ B, f x) + (∑ x ∈ B, f x) + q * m = m * m := by
    have h := Finset.sum_congr rfl hpair
    simp only [Finset.sum_add_distrib, htsum, hzero] at h
    simpa [B, Nat.card_Ioc] using h
  have ha : a n + q * m = m * m := by rw [hablock]; exact hsum
  have haq : (a n : ℚ) + (q : ℚ) * (m : ℚ) = (m : ℚ) * (m : ℚ) := by
    exact_mod_cast ha
  have hrqq : (r : ℚ) * (q : ℚ) = (m : ℚ) := by exact_mod_cast hrq
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hqq : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hd : (m : ℚ) ^ 2 - (a n : ℚ) = (q : ℚ) * (m : ℚ) := by nlinarith [haq]
  have hdpos : (0 : ℚ) < (m : ℚ) ^ 2 - (a n : ℚ) := by
    rw [hd]
    exact mul_pos hqq hmq
  change 0 < (m : ℚ) ^ 2 - (a n : ℚ) ∧
    (r : ℚ) = (m : ℚ) ^ 2 / ((m : ℚ) ^ 2 - (a n : ℚ))
  refine ⟨hdpos, (eq_div_iff (ne_of_gt hdpos)).mpr ?_⟩
  rw [hd]
  calc
    (r : ℚ) * ((q : ℚ) * (m : ℚ)) = ((r : ℚ) * (q : ℚ)) * (m : ℚ) := by ring
    _ = (m : ℚ) ^ 2 := by rw [hrqq]; ring

#print axioms result

end D5.S3.ArithSums.FerreiraOddPowerResidueRadical
