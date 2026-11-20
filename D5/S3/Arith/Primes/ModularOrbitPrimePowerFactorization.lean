/- GID: D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/ModularOrbitPrimePowerFactorization
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Canonical prime-power factorization gives the exact orbit kernel and residue count at every positive modulus. -/

import D5.S3.Arith.Primes.ModularOrbitTransientComposition
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.ModularOrbitPrimePowerFactorization

open ModularOrbitTransientComposition

/-- List each prime-power rule once, at its exact exponent in the modulus. -/
noncomputable def primePowerRules (localRule : ℕ → ℕ → OrbitRule) (M : ℕ) : List OrbitRule :=
  M.primeFactors.toList.map (fun p => localRule p (M.factorization p))

/-- Canonical result of combining the rules of all support primes of the
given modulus. The output is independent of any supplied factorization. -/
noncomputable def ruleForModulus (localRule : ℕ → ℕ → OrbitRule) (M : ℕ) : OrbitRule :=
  combined (primePowerRules localRule M)

private theorem factorInfo {M p : ℕ} (h : p ∈ M.primeFactors) :
    Nat.Prime p ∧ 0 < M.factorization p := by
  have hp := Nat.prime_of_mem_primeFactors h
  refine ⟨hp, ?_⟩
  apply Nat.pos_of_ne_zero
  rwa [← Finsupp.mem_support_iff, Nat.support_factorization]

/-- Exact prime-power rules with positive periods produce an exact rule
at every positive modulus, including one via the empty list. -/
theorem canonical_rule_spec
    (localRule : ℕ → ℕ → OrbitRule) (f : ℕ → ℤ)
    (hlocal : ∀ p b : ℕ, p.Prime → 0 < b →
      (localRule p b).modulus = p^b ∧ 0 < (localRule p b).period ∧ (localRule p b).Exact f)
    (M : ℕ) (hM : 0 < M) :
    (ruleForModulus localRule M).modulus = M ∧
      0 < (ruleForModulus localRule M).period ∧
      (ruleForModulus localRule M).Exact f := by
  let rs := primePowerRules localRule M
  change (combined rs).modulus = M ∧ 0 < (combined rs).period ∧ (combined rs).Exact f
  have hm (p : ℕ) (hp : p ∈ M.primeFactors) :
      (localRule p (M.factorization p)).modulus = p^(M.factorization p) :=
    (hlocal p _ (factorInfo hp).1 (factorInfo hp).2).1
  have hmem (r : OrbitRule) (hr : r ∈ rs) :
      0 < r.period ∧ r.Exact f := by
    change r ∈ M.primeFactors.toList.map _ at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have hp' : p ∈ M.primeFactors := Finset.mem_toList.mp hp
    exact (hlocal p _ (factorInfo hp').1 (factorInfo hp').2).2
  refine ⟨?_, combined_period_positive rs (fun r hr => (hmem r hr).1),
    exact_combined rs f (fun r hr => (hmem r hr).2)⟩
  have hpair : rs.Pairwise (fun r s => r.modulus.Coprime s.modulus) := by
    change (M.primeFactors.toList.map _).Pairwise _
    rw [List.pairwise_map]
    have hh := (List.Pairwise.and_mem).1 (M.primeFactors.nodup_toList)
    refine hh.imp ?_
    intro p q h
    have hp := Finset.mem_toList.mp h.1
    have hq := Finset.mem_toList.mp h.2.1
    rw [hm p hp, hm q hq]
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) h.2.2
  rw [combined_modulus_eq_prod rs hpair]
  change ((M.primeFactors.toList.map _).map OrbitRule.modulus).prod = M
  rw [List.map_map, Finset.prod_map_toList]
  calc
    _ = ∏ p ∈ M.primeFactors, p ^ M.factorization p :=
      Finset.prod_congr rfl hm
    _ = M := (Nat.prod_primeFactors_pow_factorization hM.ne').symm

/-- For every positive modulus the actual pairwise collision is determined
by the maximum transient and lcm of the prime-power periods. -/
theorem canonical_modulus_collision
    (localRule : ℕ → ℕ → OrbitRule) (f : ℕ → ℤ)
    (hlocal : ∀ p b : ℕ, p.Prime → 0 < b →
      (localRule p b).modulus = p^b ∧ 0 < (localRule p b).period ∧ (localRule p b).Exact f)
    (M : ℕ) (hM : 0 < M) (n m : ℕ) (hmn : m < n) :
    (f n ≡ f m [ZMOD (M:ℤ)]) ↔
      (ruleForModulus localRule M).transient ≤ m ∧ (ruleForModulus localRule M).period ∣ n-m := by
  obtain ⟨hm, _, he⟩ := canonical_rule_spec localRule f hlocal M hM
  have hn := he n m hmn
  rwa [hm] at hn

/-- For every positive modulus the residue image has exactly A+T elements,
where A and T are read from the prime-power rules. -/
theorem canonical_modulus_residue_count
    (localRule : ℕ → ℕ → OrbitRule) (f : ℕ → ℤ)
    (hlocal : ∀ p b : ℕ, p.Prime → 0 < b →
      (localRule p b).modulus = p^b ∧ 0 < (localRule p b).period ∧ (localRule p b).Exact f)
    (M : ℕ) (hM : 0 < M) :
    Nat.card {z : ℤ // ∃ n : ℕ, f n % (M:ℤ) = z} =
      (ruleForModulus localRule M).transient + (ruleForModulus localRule M).period := by
  obtain ⟨hm, hp, he⟩ := canonical_rule_spec localRule f hlocal M hM
  have hn := exact_residue_count (ruleForModulus localRule M) f he hp
  rwa [hm] at hn

end D5.S3.Arith.Primes.ModularOrbitPrimePowerFactorization
