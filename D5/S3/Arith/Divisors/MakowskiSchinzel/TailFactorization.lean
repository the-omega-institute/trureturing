/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/TailFactorization
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/TailFactorization
   mirror-E: none(waiver:unbounded-prime-family-estimate)
   anchors: []
   utility: none
   digest: Least odd prime support implies the finite reciprocal tail bound. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.TailFamily

/-! # The least odd support prime -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel

open Finset

/-- The reciprocal mass over forty-two prime predecessors is at most `1261/1368`
when their least odd prime factor is at least `131`. -/
theorem large_support_tail (Q : Finset ℕ) (r : ℕ)
    (hr : r.Prime) (hr131 : 131 ≤ r) (hcard : Q.card ≤ 42)
    (hq : ∀ q ∈ Q, q.Prime) (hrdvd : ∀ q ∈ Q, r ∣ q - 1)
    (hmin : ∀ q ∈ Q, ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ q - 1 → r ≤ s) :
    (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
      (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) +
        42 / (2 * (r + 2 : ℚ))) ∧
      ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) < 1261 / 1368 ∧
      (let M : Finset ℕ := by
         classical
         exact Q.filter (fun q => ¬∃ a b : ℕ,
           0 < b ∧ q - 1 = 2 ^ a * r ^ b)
       (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
          (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) +
            M.card / (2 * (r + 2 : ℚ))) ∧
         (r % 3 = 1 → ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
           (r : ℚ) / (3 * (r - 1 : ℚ)) + M.card / (2 * (r + 2 : ℚ)))) := by
  have hro : Odd r := hr.odd_of_ne_two (by omega)
  have hr3 : r % 3 ≠ 0 := by
    intro hz
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.dvd_of_mod_eq_zero hz)
    omega
  apply large_support_tail_of_dichotomy Q r hro hr3 hr131 hcard hq
  intro q hq'
  have hqp := hq q hq'
  have hn : q - 1 ≠ 0 := by have := hqp.two_le; omega
  have hrle : r ≤ q - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hrdvd q hq')
  have hq2 : q ≠ 2 := by omega
  have h2dvd : 2 ∣ q - 1 := even_iff_two_dvd.mp (hqp.even_sub_one hq2)
  have hr2 : r ≠ 2 := by omega
  by_cases hsup : (q - 1).primeFactors ⊆ {2, r}
  · left
    refine ⟨(q - 1).factorization 2, (q - 1).factorization r,
      hr.factorization_pos_of_dvd hn (hrdvd q hq'), ?_⟩
    have hsupp : (q - 1).factorization.support ⊆ {2, r} := by
      simpa only [Nat.support_factorization] using hsup
    have hp := (q - 1).factorization.prod_of_support_subset hsupp
      (fun p k : ℕ => p ^ k) (by simp)
    calc
      q - 1 = (q - 1).factorization.prod (fun p k : ℕ => p ^ k) :=
        (Nat.prod_factorization_pow_eq_self hn).symm
      _ = ∏ x ∈ ({2, r} : Finset ℕ), x ^ (q - 1).factorization x := hp
      _ = _ := by simp [Ne.symm hr2]
  · right
    have hex : ∃ s ∈ (q - 1).primeFactors, s ∉ ({2, r} : Finset ℕ) := by
      exact Finset.not_subset.mp hsup
    obtain ⟨s, hs, hnot⟩ := hex
    obtain ⟨hsp, hsdvd, _⟩ := Nat.mem_primeFactors.mp hs
    have hsnot : s ≠ 2 ∧ s ≠ r := by
      simpa only [mem_insert, mem_singleton, not_or] using hnot
    have hs2 := hsnot.1
    have hsr := hsnot.2
    have hrs := hmin q hq' s hsp hs2 hsdvd
    obtain ⟨u, hu⟩ := hr.odd_of_ne_two hr2
    obtain ⟨v, hv⟩ := hsp.odd_of_ne_two hs2
    have hrs2 : r + 2 ≤ s := by omega
    have h2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
    have h2s : Nat.Coprime 2 s := (Nat.coprime_primes Nat.prime_two hsp).mpr (Ne.symm hs2)
    have hrcs : Nat.Coprime r s := (Nat.coprime_primes hr hsp).mpr (Ne.symm hsr)
    have h2rdvd : 2 * r ∣ q - 1 := h2r.mul_dvd_of_dvd_of_dvd h2dvd (hrdvd q hq')
    have hprod : 2 * r * s ∣ q - 1 :=
      (h2s.mul_left hrcs).mul_dvd_of_dvd_of_dvd h2rdvd hsdvd
    exact (Nat.mul_le_mul_left (2 * r) hrs2).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod)

#print axioms large_support_tail

end D5.S3.Arith.MakowskiSchinzel
