/- GID: D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenSmallestMissingPrime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict prime decrease reduces missing-prime thresholds to the least missing prime. -/

import D5.S3.Arith.GoldenResourceOptimalInteger
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Infinite

/- Library-search audit trail (2026-09-07):
   1. D5 searches: goldenLayerMarginal, golden_layer_marginal, smallest/least/missing prime,
      minFac, log_one_add, and log (1 + ...). Found the marginal definition and
      golden_layer_strict_decrease in GoldenResourceOptimalInteger (generality I),
      golden_layer_marginal_le_inv_pow in GoldenLayerMarginalDecay, and the private
      inv_pow_div_log_lt in GoldenPrimeLayerCofinite. No cross-prime first-layer ordering
      or construction of the least prime not dividing n was found in the searched D5 tree.
   2. Pinned Mathlib v4.33.0, revision db584cd6d46c92f209a44c0f1c829460d327499d:
      searched Analysis/SpecialFunctions/Log/{Basic,Monotone,Base}, Data/Nat/Prime,
      Data/Nat/Find and ordered field/group-with-zero APIs. Exact ingredient hits reused:
      Real.log_lt_log, Real.log_pos, Nat.Prime.log_pos, inv_strictAnti₀, div_lt_div₀,
      Nat.exists_infinite_primes, Nat.find_spec and Nat.find_min'. Also found
      Real.strictMonoOn_log, Real.log_div_self_antitoneOn, Nat.minFac, Nat.minFac_prime,
      Nat.minFac_dvd and Nat.minFac_le_of_dvd. The log/x theorem has a different ratio;
      minFac minimizes divisors, not nondivisors. No theorem for log(1+1/x)/log x or the
      required least-nondivisor reduction was found. No existing ingredient is reproved.
   3. Other pinned Lean packages: searched goldenLayerMarginal, log_one_add with
      mono/anti, missingPrime/missing_prime and smallest prime; no matching declaration.
      Online Lean ecosystem search via NyxID/Tavily (explicit application/json):
      "Lean theorem log(1+1/x)/log(x) strictly decreasing smallest prime not dividing
      integer formalization", request 9789b6e9-e89c-41ae-81ca-d14c8ba29ff2, returned
      Mathematics in Lean, an Edinburgh Lean project and ordinary number theory pages.
      "site:github.com Lean smallest prime not dividing" (quoted keywords in request),
      request 754cb1d2-5ce7-42e9-a775-7906f709cf5d, returned rxdoi/Autoformalization,
      Mathlib's IMO archive, a Lean infinitude-of-primes example, Woett/Lean-files and
      lean-pitfalls. No exact Lean declaration was found in these returned results.
      Initial requests without Content-Type returned HTTP 422; only the corrected
      successful searches support the online audit. This is not an exhaustive web claim.
   4. Preregistered escape witness, unchanged: golden_layer_marginal_one_strictAnti.
      Counterfactual checked against the actual source statements: layer decrease fixes p;
      the geometric estimate bounds one marginal only from above; the cofinite estimate
      supplies an eventual cutoff. None compares two first-layer marginals. The new live
      estimate cancels the first-layer ratio, compares positive logarithmic numerators,
      and compares positive denominators. All threshold results consume this witness.
      Admission basis: escape-witness (implementation only; freezing deferred).
      Computational content: none; all statements quantify over arbitrary primes,
      positive integers and real prices, with no bounded enumeration or numeric instance.
      Consumer -> prerequisite: threshold_of_le -> strictAnti;
      threshold_iff_of_isLeast -> threshold_of_le;
      exists_smallest_missing_prime_threshold -> threshold_iff_of_isLeast. -/

namespace D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime

open D5.S3.Arith.GoldenResourceOptimalInteger

private theorem marginal_one_eq {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p 1 = Real.log (1 + (p : ℝ)⁻¹) / Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hinv : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hden : 1 - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hinv)
  unfold goldenLayerMarginal
  congr 2
  simp only [pow_one]
  apply (div_eq_iff hden).mpr
  ring

/-- First-layer marginal benefit strictly decreases as the prime increases. -/
theorem golden_layer_marginal_one_strictAnti {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) : goldenLayerMarginal q 1 < goldenLayerMarginal p 1 := by
  rw [marginal_one_eq hp, marginal_one_eq hq]
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpqReal : (p : ℝ) < q := by exact_mod_cast hpq
  have hnum : Real.log (1 + (q : ℝ)⁻¹) < Real.log (1 + (p : ℝ)⁻¹) :=
    Real.log_lt_log (by positivity) (by linarith [inv_strictAnti₀ hpPos hpqReal])
  have hnumPos : 0 < Real.log (1 + (p : ℝ)⁻¹) :=
    Real.log_pos (lt_add_of_pos_right 1 (inv_pos.mpr hpPos))
  exact div_lt_div₀ hnum (Real.log_lt_log hpPos hpqReal).le hnumPos.le hp.log_pos

/-- A first-layer threshold at one prime holds at every larger prime, at any real price. -/
theorem golden_layer_marginal_one_threshold_of_le {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≤ p) {lambda : ℝ}
    (hprice : goldenLayerMarginal q 1 ≤ lambda) : goldenLayerMarginal p 1 ≤ lambda := by
  rcases hqp.eq_or_lt with rfl | hlt
  · exact hprice
  · exact (golden_layer_marginal_one_strictAnti hq hp hlt).le.trans hprice

/-- Among primes not dividing n, the least one's threshold is equivalent to all thresholds. -/
theorem golden_missing_prime_threshold_iff_of_isLeast {n q : ℕ}
    (hq : IsLeast {p : ℕ | p.Prime ∧ ¬ p ∣ n} q) (lambda : ℝ) :
    (∀ p : ℕ, p.Prime → ¬ p ∣ n → goldenLayerMarginal p 1 ≤ lambda) ↔
      goldenLayerMarginal q 1 ≤ lambda := by
  constructor
  · intro hall
    exact hall q hq.1.1 hq.1.2
  · intro hprice p hp hpn
    exact golden_layer_marginal_one_threshold_of_le hp hq.1.1 (hq.2 ⟨hp, hpn⟩) hprice

/-- Every positive integer has a least missing prime that decides all missing-prime thresholds. -/
theorem exists_smallest_missing_prime_threshold {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℕ, IsLeast {p : ℕ | p.Prime ∧ ¬ p ∣ n} q ∧
      ∀ lambda : ℝ,
        (∀ p : ℕ, p.Prime → ¬ p ∣ n → goldenLayerMarginal p 1 ≤ lambda) ↔
          goldenLayerMarginal q 1 ≤ lambda := by
  have hex : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n := by
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, fun h => (by omega : ¬ p ≤ n) (Nat.le_of_dvd (by omega) h)⟩
  have hleast : IsLeast {p : ℕ | p.Prime ∧ ¬ p ∣ n} (Nat.find hex) :=
    ⟨Nat.find_spec hex, fun _ hp => Nat.find_min' hex hp⟩
  exact ⟨Nat.find hex, hleast, golden_missing_prime_threshold_iff_of_isLeast hleast⟩

#print axioms golden_layer_marginal_one_strictAnti
#print axioms golden_layer_marginal_one_threshold_of_le
#print axioms golden_missing_prime_threshold_iff_of_isLeast
#print axioms exists_smallest_missing_prime_threshold

end D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
