/- GID: D5/S3/ArithSums/RatajczakGcdSumParityCharacterization
   generality: I
   mirror-B: D5/B/S3/ArithSums/RatajczakGcdSumParityCharacterization
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.Data.Finset.Interval, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Data.Nat.Prime.Defs, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Both Ratajczak gcd-filtered sums are even exactly at positive multiples of eight. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace D5.S3.ArithSums.RatajczakGcdSumParityCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

def gcd2 (k m : ℕ) : ℕ :=
  Nat.gcd k m / Nat.minFac (Nat.gcd k m)

def lcd2 (k m : ℕ) : ℕ :=
  Nat.minFac (Nat.gcd k m)

def G (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), gcd2 k m

def L (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), lcd2 k m

private theorem gcd_filter_sum_mod_two (f : ℕ → ℕ) (m : ℕ) (hm : 1 < m) :
    (∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1),
        (f (Nat.gcd k m) : ZMod 2)) =
      (f m : ZMod 2) +
        if 2 ∣ m ∧ m / 2 ≠ 1 then (f (m / 2) : ZMod 2) else 0 := by
  classical
  let S := (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1)
  let T := (Finset.Icc 1 (m - 1)).filter (fun k => Nat.gcd k m ≠ 1)
  have hmS : m ∈ S := by
    simp [S]
    omega
  have hST : S.erase m = T := by
    ext k
    simp only [S, T, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hkm, ⟨hk1, hkle⟩, hgcd⟩
      exact ⟨⟨hk1, by omega⟩, hgcd⟩
    · rintro ⟨⟨hk1, hkle⟩, hgcd⟩
      exact ⟨by omega, ⟨hk1, by omega⟩, hgcd⟩
  have hpaired :
      ∑ k ∈ T with k ≠ m - k, (f (Nat.gcd k m) : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun k _ ↦ m - k)
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkT, _⟩
      rcases Finset.mem_filter.mp hkT with ⟨hkIcc, _⟩
      have hkm : k ≤ m := by
        have := (Finset.mem_Icc.mp hkIcc).2
        omega
      rw [Nat.gcd_self_sub_left hkm]
      rw [← two_mul]
      rw [show (2 : ZMod 2) = 0 by exact CharP.cast_eq_zero (ZMod 2) 2]
      exact zero_mul _
    · intro k hk _
      exact (Finset.mem_filter.mp hk).2.symm
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkT, hkne⟩
      rcases Finset.mem_filter.mp hkT with ⟨hkIcc, hgcd⟩
      rcases Finset.mem_Icc.mp hkIcc with ⟨hk1, hkle⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · rw [Nat.gcd_self_sub_left (by omega : k ≤ m)]
          exact hgcd
      · omega
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkT, _⟩
      rcases Finset.mem_filter.mp hkT with ⟨hkIcc, _⟩
      have hkm : k ≤ m := by
        have := (Finset.mem_Icc.mp hkIcc).2
        omega
      omega
  have hfixed :
      ∑ k ∈ T with k = m - k, (f (Nat.gcd k m) : ZMod 2) =
        if 2 ∣ m ∧ m / 2 ≠ 1 then (f (m / 2) : ZMod 2) else 0 := by
    by_cases hmid : 2 ∣ m ∧ m / 2 ≠ 1
    · have htwice : m / 2 * 2 = m := Nat.div_mul_cancel hmid.1
      have hqdiv : m / 2 ∣ m := ⟨2, htwice.symm⟩
      have hqT : m / 2 ∈ T := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · rw [Nat.gcd_eq_left_iff_dvd.mpr hqdiv]
          exact hmid.2
      have hqfixed : m / 2 = m - m / 2 := by omega
      have hsingleton : T.filter (fun k => k = m - k) = {m / 2} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hk⟩
          omega
        · rintro rfl
          exact ⟨hqT, hqfixed⟩
      rw [if_pos hmid]
      change ∑ k ∈ T.filter (fun k => k = m - k),
          (f (Nat.gcd k m) : ZMod 2) = _
      rw [hsingleton]
      simp only [Finset.sum_singleton]
      rw [Nat.gcd_eq_left_iff_dvd.mpr hqdiv]
    · have hempty : T.filter (fun k => k = m - k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hkT hkfixed
        apply hmid
        have htwo : 2 ∣ m := by
          exact ⟨k, by omega⟩
        have hquot : m / 2 = k := by omega
        refine ⟨htwo, ?_⟩
        intro hq
        have hgcd := (Finset.mem_filter.mp hkT).2
        rw [hquot.symm, hq] at hgcd
        simp at hgcd
      rw [if_neg hmid]
      change ∑ k ∈ T.filter (fun k => k = m - k),
          (f (Nat.gcd k m) : ZMod 2) = 0
      rw [hempty]
      exact Finset.sum_empty
  have hT :
      (∑ k ∈ T, (f (Nat.gcd k m) : ZMod 2)) =
        if 2 ∣ m ∧ m / 2 ≠ 1 then (f (m / 2) : ZMod 2) else 0 := by
    calc
      ∑ k ∈ T, (f (Nat.gcd k m) : ZMod 2) =
          (∑ k ∈ T with k = m - k, (f (Nat.gcd k m) : ZMod 2)) +
            ∑ k ∈ T with k ≠ m - k, (f (Nat.gcd k m) : ZMod 2) :=
        (Finset.sum_filter_add_sum_filter_not T (fun k => k = m - k)
          (fun k => (f (Nat.gcd k m) : ZMod 2))).symm
      _ = _ := by rw [hfixed, hpaired, add_zero]
  change (∑ k ∈ S, (f (Nat.gcd k m) : ZMod 2)) = _
  calc
    ∑ k ∈ S, (f (Nat.gcd k m) : ZMod 2) =
        (∑ k ∈ S.erase m, (f (Nat.gcd k m) : ZMod 2)) +
          (f (Nat.gcd m m) : ZMod 2) :=
      (Finset.sum_erase_add S (fun k => (f (Nat.gcd k m) : ZMod 2)) hmS).symm
    _ = (∑ k ∈ T, (f (Nat.gcd k m) : ZMod 2)) + (f m : ZMod 2) := by
      rw [hST, Nat.gcd_self]
    _ = (if 2 ∣ m ∧ m / 2 ≠ 1 then (f (m / 2) : ZMod 2) else 0) +
        (f m : ZMod 2) := by rw [hT]
    _ = _ := add_comm _ _

#eval (G 8, L 8)
#eval (G 16, L 16)
#eval (G 24, L 24)

end D5.S3.ArithSums.RatajczakGcdSumParityCharacterization
