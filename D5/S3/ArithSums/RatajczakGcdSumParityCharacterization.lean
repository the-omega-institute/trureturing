/- GID: D5/S3/ArithSums/RatajczakGcdSumParityCharacterization
   generality: I
   mirror-B: D5/B/S3/ArithSums/RatajczakGcdSumParityCharacterization
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Both Ratajczak gcd-filtered sums are even exactly at positive multiples of eight. -/

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

theorem result : ∀ m : ℕ, 1 < m → ((Even (G m) ∧ Even (L m)) ↔ 8 ∣ m) := by
  intro m hm
  have hG :
      (G m : ZMod 2) =
        (m / Nat.minFac m : ZMod 2) +
          if 2 ∣ m ∧ m / 2 ≠ 1 then
            (m / 2 / Nat.minFac (m / 2) : ZMod 2)
          else 0 := by
    calc
      (G m : ZMod 2) =
          ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1),
            (gcd2 k m : ZMod 2) := by
        unfold G
        exact map_sum (Nat.castAddMonoidHom (ZMod 2)) _ _
      _ = _ := by
        simpa only [gcd2] using
          gcd_filter_sum_mod_two (fun d => d / Nat.minFac d) m hm
  have hL :
      (L m : ZMod 2) =
        (Nat.minFac m : ZMod 2) +
          if 2 ∣ m ∧ m / 2 ≠ 1 then
            (Nat.minFac (m / 2) : ZMod 2)
          else 0 := by
    calc
      (L m : ZMod 2) =
          ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1),
            (lcd2 k m : ZMod 2) := by
        unfold L
        exact map_sum (Nat.castAddMonoidHom (ZMod 2)) _ _
      _ = _ := by
        simpa only [lcd2] using gcd_filter_sum_mod_two Nat.minFac m hm
  have even_iff_cast_zero (n : ℕ) : Even n ↔ (n : ZMod 2) = 0 := by
    rw [even_iff_two_dvd]
    exact (ZMod.natCast_eq_zero_iff n 2).symm
  have minFac_cast_zero_imp_two_dvd (n : ℕ) (hn : n ≠ 1)
      (hz : (Nat.minFac n : ZMod 2) = 0) : 2 ∣ n := by
    have hfac : 2 ∣ Nat.minFac n :=
      (ZMod.natCast_eq_zero_iff (Nat.minFac n) 2).mp hz
    have hp : Nat.Prime (Nat.minFac n) := Nat.minFac_prime hn
    have heq : Nat.minFac n = 2 := by
      rcases (Nat.dvd_prime hp).mp hfac with h | h
      · omega
      · omega
    exact (Nat.minFac_eq_two_iff n).mp heq
  constructor
  · rintro ⟨hGeven, hLeven⟩
    have hG0 : (G m : ZMod 2) = 0 := (even_iff_cast_zero (G m)).mp hGeven
    have hL0 : (L m : ZMod 2) = 0 := (even_iff_cast_zero (L m)).mp hLeven
    by_cases h2 : 2 ∣ m
    · by_cases hqone : m / 2 = 1
      · have hm2 : m = 2 := by
          have htwice := Nat.div_mul_cancel h2
          omega
        subst m
        exact ((by decide : ¬Even (G 2)) hGeven).elim
      · have hmid : 2 ∣ m ∧ m / 2 ≠ 1 := ⟨h2, hqone⟩
        have hmf_m : Nat.minFac m = 2 := (Nat.minFac_eq_two_iff m).mpr h2
        by_cases h4 : 4 ∣ m
        · have hq2 : 2 ∣ m / 2 := by
            rcases h4 with ⟨a, ha⟩
            exact ⟨a, by omega⟩
          have hmf_q : Nat.minFac (m / 2) = 2 :=
            (Nat.minFac_eq_two_iff (m / 2)).mpr hq2
          have hGeq :
              (G m : ZMod 2) =
                ((m / 2 : ℕ) : ZMod 2) + ((m / 2 / 2 : ℕ) : ZMod 2) := by
            simpa only [if_pos hmid, hmf_m, hmf_q] using hG
          have hq0 : ((m / 2 : ℕ) : ZMod 2) = 0 :=
            (ZMod.natCast_eq_zero_iff (m / 2) 2).mpr hq2
          have hquarter0 : ((m / 2 / 2 : ℕ) : ZMod 2) = 0 := by
            have hsum := hGeq.symm.trans hG0
            rw [hq0, zero_add] at hsum
            exact hsum
          have hquarter2 : 2 ∣ m / 2 / 2 :=
            (ZMod.natCast_eq_zero_iff (m / 2 / 2) 2).mp hquarter0
          rcases hquarter2 with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          have hhalf_twice := Nat.div_mul_cancel h2
          have hquarter_twice := Nat.div_mul_cancel hq2
          omega
        · have hqodd : ¬2 ∣ m / 2 := by
            intro hq2
            apply h4
            rcases hq2 with ⟨a, ha⟩
            refine ⟨a, ?_⟩
            have hhalf_twice := Nat.div_mul_cancel h2
            omega
          have hLeq :
              (L m : ZMod 2) =
                ((2 : ℕ) : ZMod 2) + (Nat.minFac (m / 2) : ZMod 2) := by
            simpa only [if_pos hmid, hmf_m] using hL
          have hqfac0 : (Nat.minFac (m / 2) : ZMod 2) = 0 := by
            have hsum := hLeq.symm.trans hL0
            rw [show ((2 : ℕ) : ZMod 2) = 0 by exact CharP.cast_eq_zero (ZMod 2) 2,
              zero_add] at hsum
            exact hsum
          exact (hqodd (minFac_cast_zero_imp_two_dvd (m / 2) hqone hqfac0)).elim
    · have hnotmid : ¬(2 ∣ m ∧ m / 2 ≠ 1) := fun h => h2 h.1
      have hLeq : (L m : ZMod 2) = (Nat.minFac m : ZMod 2) := by
        simpa only [if_neg hnotmid, add_zero] using hL
      have hfac0 : (Nat.minFac m : ZMod 2) = 0 := hLeq.symm.trans hL0
      have hm1 : m ≠ 1 := by omega
      exact (h2 (minFac_cast_zero_imp_two_dvd m hm1 hfac0)).elim
  · intro h8
    rcases h8 with ⟨a, ha⟩
    have h2 : 2 ∣ m := ⟨4 * a, by omega⟩
    have hq2 : 2 ∣ m / 2 := ⟨2 * a, by omega⟩
    have hquarter2 : 2 ∣ m / 2 / 2 := ⟨a, by omega⟩
    have hqone : m / 2 ≠ 1 := by omega
    have hmid : 2 ∣ m ∧ m / 2 ≠ 1 := ⟨h2, hqone⟩
    have hmf_m : Nat.minFac m = 2 := (Nat.minFac_eq_two_iff m).mpr h2
    have hmf_q : Nat.minFac (m / 2) = 2 :=
      (Nat.minFac_eq_two_iff (m / 2)).mpr hq2
    have hGeq :
        (G m : ZMod 2) =
          ((m / 2 : ℕ) : ZMod 2) + ((m / 2 / 2 : ℕ) : ZMod 2) := by
      simpa only [if_pos hmid, hmf_m, hmf_q] using hG
    have hLeq :
        (L m : ZMod 2) = ((2 : ℕ) : ZMod 2) + ((2 : ℕ) : ZMod 2) := by
      simpa only [if_pos hmid, hmf_m, hmf_q] using hL
    have hq0 : ((m / 2 : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff (m / 2) 2).mpr hq2
    have hquarter0 : ((m / 2 / 2 : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff (m / 2 / 2) 2).mpr hquarter2
    have hG0 : (G m : ZMod 2) = 0 := by
      rw [hGeq, hq0, hquarter0, add_zero]
    have hL0 : (L m : ZMod 2) = 0 := by
      rw [hLeq]
      rw [show ((2 : ℕ) : ZMod 2) = 0 by exact CharP.cast_eq_zero (ZMod 2) 2,
        zero_add]
    exact ⟨(even_iff_cast_zero (G m)).mpr hG0,
      (even_iff_cast_zero (L m)).mpr hL0⟩

#print axioms gcd2
#print axioms lcd2
#print axioms G
#print axioms L
#print axioms result

end D5.S3.ArithSums.RatajczakGcdSumParityCharacterization
