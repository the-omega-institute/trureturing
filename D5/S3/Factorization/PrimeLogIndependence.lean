/- GID: D5/S3/Factorization/PrimeLogIndependence
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimeLogIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The logarithms of the primes are linearly independent over the integers: for a finite set S of primes and integer coefficients k, if the weighted sum of log p over S vanishes then every coefficient is zero. The vanishing sum exponentiates to a product of prime powers equal to one, which unique factorization forces to be empty. -/

import Mathlib

namespace D5.S3.Factorization.PrimeLogIndependence

open Finset

/-- The prime-power factorization of `∏_{p ∈ S} p ^ a p` reads off the exponent `a q` at a prime
`q ∈ S`, because distinct primes have disjoint factorization supports. -/
private theorem factorization_prod_pow_prime (S : Finset ℕ) (a : ℕ → ℕ)
    (hp : ∀ p ∈ S, p.Prime) (q : ℕ) (hq : q ∈ S) :
    (∏ p ∈ S, p ^ a p).factorization q = a q := by
  have hne : ∀ p ∈ S, p ^ a p ≠ 0 := fun p hpS => pow_ne_zero _ (hp p hpS).ne_zero
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply, Finset.sum_eq_single q]
  · rw [Nat.factorization_pow, Finsupp.smul_apply, (hp q hq).factorization]; simp
  · intro p hpS hpq
    rw [Nat.factorization_pow, Finsupp.smul_apply, (hp p hpS).factorization, Finsupp.single_apply,
      if_neg hpq]; simp
  · intro h; exact absurd hq h

/-- Off the index set, `∏_{p ∈ S} p ^ a p` has zero factorization exponent. -/
private theorem factorization_prod_pow_prime_notmem (S : Finset ℕ) (a : ℕ → ℕ)
    (hp : ∀ p ∈ S, p.Prime) (q : ℕ) (hq : q ∉ S) :
    (∏ p ∈ S, p ^ a p).factorization q = 0 := by
  have hne : ∀ p ∈ S, p ^ a p ≠ 0 := fun p hpS => pow_ne_zero _ (hp p hpS).ne_zero
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero (fun p hpS => ?_)
  have hpq : p ≠ q := fun h => hq (h ▸ hpS)
  rw [Nat.factorization_pow, Finsupp.smul_apply, (hp p hpS).factorization, Finsupp.single_apply,
    if_neg hpq]; simp

/-- Equal prime-power products over disjoint prime sets force the exponents on the first set to zero. -/
private theorem disjoint_prod_pow_eq (A B : Finset ℕ) (a b : ℕ → ℕ) (hpA : ∀ p ∈ A, p.Prime)
    (hpB : ∀ p ∈ B, p.Prime) (hd : Disjoint A B)
    (h : ∏ p ∈ A, p ^ a p = ∏ p ∈ B, p ^ b p) : ∀ q ∈ A, a q = 0 := by
  intro q hqA
  have hqB : q ∉ B := Finset.disjoint_left.mp hd hqA
  have e1 := factorization_prod_pow_prime A a hpA q hqA
  have e2 := factorization_prod_pow_prime_notmem B b hpB q hqB
  rw [h, e2] at e1
  exact e1.symm

/-- Exponentiating a nonnegative-integer log-combination gives the corresponding prime-power product. -/
private theorem exp_sum_log_eq_prod (T : Finset ℕ) (c : ℕ → ℕ) (hp : ∀ p ∈ T, p.Prime) :
    Real.exp (∑ p ∈ T, (c p : ℝ) * Real.log p) = ∏ p ∈ T, (p : ℝ) ^ c p := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun p hpT => ?_)
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (hp p hpT).pos)]

/-- **Integer linear independence of prime logarithms.** For a finite set `S` of primes and integer
coefficients `k`, if `∑_{p ∈ S} k p · log p = 0` then every `k p` is zero. Splitting `S` by the sign of
`k` and exponentiating turns the vanishing sum into an equality of prime-power products over the
positive and negative index sets; these sets are disjoint sets of primes, so unique factorization
forces every exponent — hence every coefficient — to vanish. -/
theorem prime_log_indep (S : Finset ℕ) (k : ℕ → ℤ) (hp : ∀ p ∈ S, p.Prime)
    (h : ∑ p ∈ S, (k p : ℝ) * Real.log p = 0) : ∀ p ∈ S, k p = 0 := by
  classical
  set A := S.filter (fun p => 0 ≤ k p) with hAdef
  set B := S.filter (fun p => ¬ (0 ≤ k p)) with hBdef
  have hAB : Disjoint A B := Finset.disjoint_filter_filter_not S S _
  have hpA : ∀ p ∈ A, p.Prime := fun p hpm => hp p (Finset.mem_filter.mp hpm).1
  have hpB : ∀ p ∈ B, p.Prime := fun p hpm => hp p (Finset.mem_filter.mp hpm).1
  have hsplit : (∑ p ∈ A, (k p : ℝ) * Real.log p) + (∑ p ∈ B, (k p : ℝ) * Real.log p) = 0 := by
    rw [hAdef, hBdef, Finset.sum_filter_add_sum_filter_not]; exact h
  have hAeq : (∑ p ∈ A, ((k p).toNat : ℝ) * Real.log p) = ∑ p ∈ A, (k p : ℝ) * Real.log p := by
    refine Finset.sum_congr rfl (fun p hpm => ?_)
    have hkp : 0 ≤ k p := (Finset.mem_filter.mp hpm).2
    have : ((k p).toNat : ℝ) = (k p : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hkp
    rw [this]
  have hBeq : (∑ p ∈ B, ((-k p).toNat : ℝ) * Real.log p) = -(∑ p ∈ B, (k p : ℝ) * Real.log p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hpm => ?_)
    have hkp : k p < 0 := lt_of_not_ge (Finset.mem_filter.mp hpm).2
    have : ((-k p).toNat : ℝ) = ((-k p : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -k p)
    rw [this]; push_cast; ring
  have hreal : (∑ p ∈ A, ((k p).toNat : ℝ) * Real.log p)
      = ∑ p ∈ B, ((-k p).toNat : ℝ) * Real.log p := by
    rw [hAeq, hBeq]; linarith [hsplit]
  have hprodR : (∏ p ∈ A, (p : ℝ) ^ (k p).toNat) = ∏ p ∈ B, (p : ℝ) ^ (-k p).toNat := by
    rw [← exp_sum_log_eq_prod A _ hpA, ← exp_sum_log_eq_prod B _ hpB, hreal]
  have hprodN : (∏ p ∈ A, p ^ (k p).toNat) = ∏ p ∈ B, p ^ (-k p).toNat := by
    have hc : ((∏ p ∈ A, p ^ (k p).toNat : ℕ) : ℝ) = ((∏ p ∈ B, p ^ (-k p).toNat : ℕ) : ℝ) := by
      push_cast; exact hprodR
    exact_mod_cast hc
  have hAzero := disjoint_prod_pow_eq A B (fun p => (k p).toNat) (fun p => (-k p).toNat)
    hpA hpB hAB hprodN
  have hBzero := disjoint_prod_pow_eq B A (fun p => (-k p).toNat) (fun p => (k p).toNat)
    hpB hpA hAB.symm hprodN.symm
  intro q hqS
  by_cases hk : 0 ≤ k q
  · have hqA : q ∈ A := Finset.mem_filter.mpr ⟨hqS, hk⟩
    have := hAzero q hqA; omega
  · have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqS, hk⟩
    have := hBzero q hqB; omega

end D5.S3.Factorization.PrimeLogIndependence
