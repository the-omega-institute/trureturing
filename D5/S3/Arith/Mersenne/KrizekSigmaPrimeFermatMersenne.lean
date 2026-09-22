/- GID: D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne
   generality: G
   mirror-B: D5/B/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Fermat]
   utility: none
   digest: Prime divisor sum forces a Fermat input and a Mersenne divisor sum. -/

import Mathlib.NumberTheory.Fermat

namespace D5.S3.Arith.Mersenne.KrizekSigmaPrimeFermatMersenne

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ArithmeticFunction.sigma in
/-- If the divisor sum of `m` is prime then `m` is a prime power. -/
theorem sigma_one_prime_imp_prime_pow {m : ℕ} (h : (σ 1 m).Prime) :
    ∃ q k : ℕ, q.Prime ∧ 1 ≤ k ∧ m = q ^ k := by
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    exact h.ne_zero rfl
  have hm1 : m ≠ 1 := by
    intro hm
    subst m
    simpa using h.ne_one
  have hm2 : 2 ≤ m := by omega
  let f : ℕ → ℕ := fun p =>
    ∑ i ∈ Finset.range (m.factorization p + 1), p ^ i
  have hsigma : σ 1 m = ∏ p ∈ m.primeFactors, f p := by
    simpa only [f, mul_one] using
      (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) hm0)
  have hf_gt_one (p : ℕ) (hp : p ∈ m.primeFactors) : 1 < f p := by
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hePos : 0 < m.factorization p :=
      hpPrime.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
    have hsubset : Finset.range 2 ⊆
        Finset.range (m.factorization p + 1) :=
      Finset.range_mono (by omega)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => Nat.zero_le (p ^ i))
    change (∑ i ∈ Finset.range 2, p ^ i) ≤ f p at hle
    norm_num [Finset.sum_range_succ] at hle
    have hp2 := hpPrime.two_le
    omega
  obtain ⟨q, hqMem⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
  have hprodPrime : (∏ p ∈ m.primeFactors, f p).Prime := by
    rwa [← hsigma]
  rw [← Finset.mul_prod_erase m.primeFactors f hqMem] at hprodPrime
  rcases Nat.prime_mul_iff.mp hprodPrime with hleft | hright
  · have herase : m.primeFactors.erase q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hdiv : f r ∣ ∏ p ∈ m.primeFactors.erase q, f p :=
        Finset.dvd_prod_of_mem f hr
      rw [hleft.2] at hdiv
      exact (ne_of_gt (hf_gt_one r (Finset.mem_of_mem_erase hr))) (Nat.dvd_one.mp hdiv)
    have hsingleton : m.primeFactors = {q} := by
      rw [← Finset.insert_erase hqMem, herase]
      rfl
    have hprimePow : IsPrimePow m :=
      isPrimePow_iff_card_primeFactors_eq_one.mpr (by simp [hsingleton])
    obtain ⟨r, k, hrPrime, hk, hrPow⟩ := (isPrimePow_nat_iff m).mp hprimePow
    exact ⟨r, k, hrPrime, hk, hrPow.symm⟩
  · exact ((ne_of_gt (hf_gt_one q hqMem)) hright.2).elim

open scoped ArithmeticFunction.sigma in
theorem result {p : ℕ} (hp : p.Prime) (hq : (σ 1 (p - 1)).Prime) :
    (∃ m : ℕ, p = 2 ^ 2 ^ m + 1) ∧ (∃ r : ℕ, r.Prime ∧ σ 1 (p - 1) = 2 ^ r - 1) := by
  have hpNeTwo : p ≠ 2 := by
    intro hpTwo
    subst p
    apply hq.ne_one
    norm_num [ArithmeticFunction.sigma_one]
  obtain ⟨q, k, hqPrime, hk, hpk⟩ :=
    sigma_one_prime_imp_prime_pow hq
  have htwoDvd : 2 ∣ p - 1 :=
    even_iff_two_dvd.mp (hp.even_sub_one hpNeTwo)
  have htwoDvdPow : 2 ∣ q ^ k := by rwa [← hpk]
  have htwoDvdQ : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow htwoDvdPow
  have hqTwo : q = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqPrime).mp htwoDvdQ).symm
  subst q
  have hpPow : p = 2 ^ k + 1 := by
    have hp2 := hp.two_le
    omega
  have hk0 : k ≠ 0 := by omega
  obtain ⟨m, hm⟩ :=
    Nat.pow_of_pow_add_prime (a := 2) (n := k) (by norm_num) hk0 (by
      rw [← hpPow]
      exact hp)
  have hgeom :
      (∑ i ∈ Finset.range (k + 1), 2 ^ i) = 2 ^ (k + 1) - 1 := by
    simpa using (geom_sum_mul_of_one_le (x := (2 : ℕ)) (by norm_num) (k + 1))
  have hsigmaMersenne : σ 1 (p - 1) = 2 ^ (k + 1) - 1 := by
    calc
      σ 1 (p - 1) = σ 1 (2 ^ k) := by rw [hpk]
      _ = ∑ i ∈ Finset.range (k + 1), 2 ^ i :=
        ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two
      _ = 2 ^ (k + 1) - 1 := hgeom
  have hmPrime : (2 ^ (k + 1) - 1).Prime := by
    rw [← hsigmaMersenne]
    exact hq
  have hkSuccPrime : (k + 1).Prime :=
    (Nat.prime_of_pow_sub_one_prime (a := 2) (n := k + 1)
      (by omega) hmPrime).2
  constructor
  · refine ⟨m, ?_⟩
    simpa only [hm] using hpPow
  · exact ⟨k + 1, hkSuccPrime, hsigmaMersenne⟩

end D5.S3.Arith.Mersenne.KrizekSigmaPrimeFermatMersenne
