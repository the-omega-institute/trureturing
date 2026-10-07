/- GID: D5/S3/Arith/Covering/PrimeSupportGapDescent
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrimeSupportGapDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimal odd covers have no smaller-prime support gap. -/

import D5.S3.Arith.Congruence.ConditionalComparison.AdjacentProfileExchange
import D5.S3.Arith.Covering.PrimeFactorPureClass
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

private theorem prime_dvd_finset_lcm_exists {ι : Type*} (s : Finset ι)
    (f : ι → ℕ) (p : ℕ) (hp : Nat.Prime p)
    (h : p ∣ s.lcm f) : ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.lcm_empty, Nat.dvd_one] at h
      exact False.elim (hp.ne_one h)
  | @insert a s ha ih =>
      have hlcm : p ∣ Nat.lcm (f a) (s.lcm f) := by
        rw [Finset.lcm_insert] at h
        exact h
      rcases hp.dvd_or_dvd_of_dvd_lcm hlcm with hfa | hrest
      · exact ⟨a, by simp, hfa⟩
      · obtain ⟨i, hi, hfi⟩ := ih hrest
        exact ⟨i, Finset.mem_insert_of_mem hi, hfi⟩

theorem no_gap_in_prime_support
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpodd : Odd p)
    (hpq : p < q) (hpAbsent : ¬ p ∣ F.commonModulus)
    (hqPresent : q ∣ F.commonModulus) : False := by
  classical
  have hcommon0 := F.commonModulus_ne_zero
  obtain ⟨G, W, hqW, hcommon⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hcommon0 q hq.ne_one
  have hG : 0 < G := by
    by_contra hG
    have hG0 : G = 0 := Nat.eq_zero_of_not_pos hG
    apply hqW
    obtain ⟨c, hc⟩ := hqPresent
    rw [hG0, pow_zero, one_mul] at hcommon
    rw [hcommon] at hc
    exact ⟨c, hc⟩
  have hpW : ¬ p ∣ W := by
    intro hpW
    apply hpAbsent
    rw [hcommon]
    exact dvd_mul_of_dvd_right hpW _
  have hW : Nat.Coprime W (p * q) := by
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · exact (hp.coprime_iff_not_dvd.mpr hpW).symm
    · exact (hq.coprime_iff_not_dvd.mpr hqW).symm
  have hperiod : ∀ i, F.modulus i ∣ q ^ G * W := by
    intro i
    rw [← hcommon]
    exact F.modulus_dvd_commonModulus i
  obtain ⟨i, hi, hqi⟩ := prime_dvd_finset_lcm_exists
    (Finset.univ : Finset (Fin L)) F.modulus q hq hqPresent
  have hqClass : ∃ j : Fin L, F.modulus j = q := by
    obtain ⟨j, hj⟩ := prime_dvd_modulus_is_present F hsumMin i q hq hqi
    exact ⟨j, hj⟩
  obtain ⟨donor, hdonor⟩ := hqClass
  have hpAbsentMod : ∀ i, ¬ p ∣ F.modulus i := by
    intro i hpi
    apply hpAbsent
    exact hpi.trans (F.modulus_dvd_commonModulus i)
  have htail : ∀ i, 0 < (F.modulus i).factorization q →
      (F.modulus i).factorization p ≤ 0 := by
    intro i hi
    rw [Nat.factorization_eq_zero_of_not_dvd (hpAbsentMod i)]
  have hcut : ∀ i, (F.modulus i).factorization q = 0 →
      (F.modulus i).factorization p ≤ 0 := by
    intro i hi
    rw [Nat.factorization_eq_zero_of_not_dvd (hpAbsentMod i)]
  obtain ⟨L', modulus', residue', hcover', hnonunit', hlt, hsum', hinj', hodd'⟩ :=
    Erdos7.adjacent_profile_exchange (p := p) (q := q) (H := 0) (G := G)
      (W := W) (k := 0) (A := 0) (B := 0)
      F.modulus F.residue F.covers F.modulus_one_lt hp hq hpodd hW
      (by intro i; simpa using hperiod i)
      htail hcut donor (by simpa [hdonor]) (by simpa using hpq)
  let H : OddDistinctCoveringSystem L' :=
    { modulus := modulus'
      residue := residue'
      covers := hcover'
      modulus_one_lt := hnonunit'
      modulus_odd := by
        intro i
        exact hodd' (fun j => F.modulus_odd j) i
      modulus_injective := hinj' F.modulus_injective }
  exact (Nat.not_lt_of_ge (hcountMin H)) hlt

end Erdos7.OddDistinctCoveringSystem
