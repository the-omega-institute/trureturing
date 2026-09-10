/- GID: D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/FirstLayerMarginalAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime antitonicity reduces the upper layer price to an explicit finite maximum. -/

import D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
import D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval

/- Library-search audit trail (2026-09-08):
   1. D5 searches found the frozen prime-antitonicity owner
      `GoldenSmallestMissingPrime.golden_layer_marginal_one_strictAnti` and the
      attained-supremum specification `GoldenResourcePriceInterval.golden_upper_price_spec`.
      Both are applied below; no second proof of prime antitonicity is introduced.
   2. Pinned Mathlib searches found `Finset.le_max'`, `Finset.max'_le`,
      `Nat.mem_primeFactors`, and `Nat.factorization_eq_zero_of_not_dvd`.
      These give the finite maximum once the least missing prime controls all
      primes outside the factor support.
   3. The successor-log identity is retained as the exact bridge between the
      frozen first-layer marginal and the requested logarithmic quotient. -/

namespace D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
open D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval
open Finset

/-- Splitting `x + 1 = x * (1 + 1/x)` separates the successor-log quotient. -/
theorem log_add_one_div_log_eq_one_add {x : ℝ} (hx : 1 < x) :
    Real.log (x + 1) / Real.log x =
      1 + Real.log (1 + 1 / x) / Real.log x := by
  have hxNe : x ≠ 0 := ne_of_gt (by linarith)
  have hOneAddNe : 1 + 1 / x ≠ 0 := ne_of_gt (by positivity)
  have hFactor : x + 1 = x * (1 + 1 / x) := by
    field_simp
  have hLogNe : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [hFactor, Real.log_mul hxNe hOneAddNe]
  field_simp

/-- The first golden layer is the normalized logarithmic quotient. -/
theorem golden_layer_marginal_one_eq_log_one_add_inv {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p 1 = Real.log (1 + 1 / (p : ℝ)) / Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hInv : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hDenominator : 1 - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hInv)
  unfold goldenLayerMarginal
  congr 2
  simp only [pow_one, one_div]
  apply (div_eq_iff hDenominator).mpr
  ring

/-- For increasing primes, the successor-log quotient strictly decreases. -/
theorem log_add_one_div_log_strictAnti_of_prime {p q : ℕ} (hp : p.Prime)
    (hp2 : 2 ≤ p) (hq : q.Prime) (hpq : p < q) :
    Real.log (q + 1) / Real.log q < Real.log (p + 1) / Real.log p := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  rw [log_add_one_div_log_eq_one_add hqReal, log_add_one_div_log_eq_one_add hpReal]
  rw [← golden_layer_marginal_one_eq_log_one_add_inv hq,
    ← golden_layer_marginal_one_eq_log_one_add_inv hp]
  linarith only [GoldenSmallestMissingPrime.golden_layer_marginal_one_strictAnti hp hq hpq]

private theorem missing_prime_next_layer_le {n p q : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n)
    (hq : IsLeast {r : ℕ | r.Prime ∧ ¬r ∣ n} q) :
    goldenLayerMarginal p (n.factorization p + 1) ≤
      goldenLayerMarginal q (n.factorization q + 1) := by
  rw [Nat.factorization_eq_zero_of_not_dvd hpn,
    Nat.factorization_eq_zero_of_not_dvd hq.1.2, zero_add]
  exact GoldenSmallestMissingPrime.golden_layer_marginal_one_threshold_of_le hp hq.1.1
    (hq.2 ⟨hp, hpn⟩) le_rfl

/-- The upper layer price is a maximum over the prime support and its least missing prime. -/
theorem golden_upper_price_eq_finite_max_of_isLeast_missing_prime {n q : ℕ} (hn : 1 ≤ n)
    (hq : IsLeast {p : ℕ | p.Prime ∧ ¬p ∣ n} q) :
    goldenUpperPrice n =
      ((insert q n.primeFactors).image fun p =>
        goldenLayerMarginal p (n.factorization p + 1)).max' (by simp) := by
  classical
  obtain ⟨p, hp, hupperEq, hupper⟩ := golden_upper_price_spec hn
  apply le_antisymm
  · rw [hupperEq]
    by_cases hpn : p ∣ n
    · apply Finset.le_max'
      exact Finset.mem_image.mpr
        ⟨p, Finset.mem_insert_of_mem (hp.mem_primeFactors hpn (by omega)), rfl⟩
    · have hqMax : goldenLayerMarginal q (n.factorization q + 1) ≤
          ((insert q n.primeFactors).image fun r =>
            goldenLayerMarginal r (n.factorization r + 1)).max' (by simp) := by
        apply Finset.le_max'
        exact Finset.mem_image.mpr ⟨q, Finset.mem_insert_self q n.primeFactors, rfl⟩
      exact (missing_prime_next_layer_le hp hpn hq).trans hqMax
  · apply Finset.max'_le
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_insert.mp hp with hpq | hp
    · simpa [hpq] using hupper q hq.1.1
    · exact hupper p (Nat.prime_of_mem_primeFactors hp)

/-- The upper layer price is a finite maximum, with the least missing prime produced here. -/
theorem golden_upper_price_eq_finite_max {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℕ, IsLeast {p : ℕ | p.Prime ∧ ¬p ∣ n} q ∧
      goldenUpperPrice n =
        ((insert q n.primeFactors).image fun p =>
          goldenLayerMarginal p (n.factorization p + 1)).max' (by simp) := by
  obtain ⟨q, hq, -⟩ := GoldenSmallestMissingPrime.exists_smallest_missing_prime_threshold hn
  exact ⟨q, hq, golden_upper_price_eq_finite_max_of_isLeast_missing_prime hn hq⟩

#print axioms log_add_one_div_log_eq_one_add
#print axioms golden_layer_marginal_one_eq_log_one_add_inv
#print axioms log_add_one_div_log_strictAnti_of_prime
#print axioms golden_upper_price_eq_finite_max_of_isLeast_missing_prime
#print axioms golden_upper_price_eq_finite_max

end D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
