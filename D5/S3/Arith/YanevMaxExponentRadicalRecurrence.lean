/- GID: D5/S3/Arith/YanevMaxExponentRadicalRecurrence
   generality: I
   mirror-B: D5/B/S3/Arith/YanevMaxExponentRadicalRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Yanev's maximum prime exponent decreases by one after division by the radical. -/

import D5.S1.Deficit.AlmostAdditivity

namespace D5.S3.Arith.YanevMaxExponentRadicalRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Deficit.AlmostAdditivity (primeRadical)

/-- A051903: maximum exponent in the prime factorization, with empty maximum zero. -/
def a (n : ℕ) : ℕ := n.primeFactors.sup n.factorization

/-- Yanev's recurrence and base value determine the sequence on positive indices. -/
theorem result :
    a 1 = 0 ∧ (∀ n : ℕ, 1 < n → a n = a (n / primeRadical n) + 1) ∧
    ∀ b : ℕ → ℕ, b 1 = 0 → (∀ n : ℕ, 1 < n → b n = b (n / primeRadical n) + 1) →
      ∀ n : ℕ, 0 < n → b n = a n := by
  classical
  have hbase : a 1 = 0 := by simp [a]
  have hrec : ∀ n : ℕ, 1 < n → a n = a (n / primeRadical n) + 1 := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hrad_dvd : primeRadical n ∣ n := Nat.prod_primeFactors_dvd n
    have hrad_factor (p : ℕ) (hp : p ∈ n.primeFactors) :
        (primeRadical n).factorization p = 1 := by
      rw [primeRadical, Nat.factorization_prod_apply
        (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero)]
      rw [Finset.sum_eq_single p]
      · exact (Nat.prime_of_mem_primeFactors hp).factorization_self
      · intro q hq hqp
        simp [(Nat.prime_of_mem_primeFactors hq).factorization,
          Ne.symm hqp]
      · simp [hp]
    have hsubset : (n / primeRadical n).primeFactors ⊆ n.primeFactors :=
      Nat.primeFactors_mono (Nat.div_dvd_of_dvd hrad_dvd) hn0
    have hsup : a (n / primeRadical n) = n.primeFactors.sup (n / primeRadical n).factorization := by
      apply le_antisymm
      · exact Finset.sup_mono hsubset
      · apply Finset.sup_le
        intro p _hp
        by_cases hpm : p ∈ (n / primeRadical n).primeFactors
        · exact Finset.le_sup hpm
        · have hz : (n / primeRadical n).factorization p = 0 :=
            Finsupp.notMem_support_iff.mp hpm
          rw [hz]
          exact Nat.zero_le _
    rw [hsup, Finset.sup_add (Nat.nonempty_primeFactors.mpr hn)]
    apply Finset.sup_congr rfl
    intro p hp
    have he : 0 < n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    rw [Nat.factorization_div hrad_dvd, Finsupp.tsub_apply, hrad_factor p hp]
    omega
  refine ⟨hbase, hrec, ?_⟩
  intro b hb1 hb n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn0
    by_cases hn1 : n = 1
    · subst n
      exact hb1.trans hbase.symm
    have hn : 1 < n := by omega
    have hrad_dvd : primeRadical n ∣ n := Nat.prod_primeFactors_dvd n
    have hrad_pos : 0 < primeRadical n := Nat.pos_of_dvd_of_pos hrad_dvd hn0
    have hrad1 : 1 < primeRadical n := by
      obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
      exact lt_of_lt_of_le (Nat.prime_of_mem_primeFactors hp).one_lt
        (Nat.le_of_dvd hrad_pos (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp))
    have hlt : n / primeRadical n < n := Nat.div_lt_self hn0 hrad1
    have hpos : 0 < n / primeRadical n :=
      Nat.div_pos (Nat.le_of_dvd hn0 hrad_dvd) hrad_pos
    rw [hb n hn, hrec n hn, ih (n / primeRadical n) hlt hpos]

end D5.S3.Arith.YanevMaxExponentRadicalRecurrence
