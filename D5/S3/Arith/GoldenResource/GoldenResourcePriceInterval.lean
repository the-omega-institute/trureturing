/- GID: D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResourcePriceInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An attained upper layer price and a lower layer price characterize colossal abundance. -/

import D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
import D5.S3.Arith.GoldenPrimeLayerCofinite
import Mathlib.Data.Finset.Max

/- Library-search audit trail (2026-09-07):
   1. D5 searches for goldenUpperPrice, goldenLowerPrice, IsColossallyAbundant,
      golden_upper_price_attained, colossally_abundant_iff, and marginal positivity found
      no matching declaration. The frozen fixed-price criterion and uniform prime cutoff
      above are reused directly. GoldenFutureExtensionMaximum maximizes integer extensions,
      not the next-layer marginal over primes. Both direct D5 imports have generality I.
   2. Pinned Mathlib v4.33.0 searches for colossally, goldenLayer, goldenResource, and finite
      extrema found no specialized theorem. Finset.exists_max_image, Finset.le_inf',
      Finset.inf'_le, csSup_le, le_csSup, and Nat.mem_primeFactors provide generic components.
   3. Third-party Lean ecosystem, NyxID/Firecrawl: exact query
      "golden_upper_price_attained" OR "goldenLayerMarginal" Lean returned no web results.
      Query "Lean theorem prover colossally abundant price interval maximum prime marginal"
      returned generic Lean pages and the Wikipedia colossal-abundance article, with no
      matching Lean declaration in the returned results. A prior catalog lookup for
      api-tavily returned 404 and is not counted as a search.
   4. New step: use the positive next layer at 2 to obtain a uniform cutoff, take a finite
      maximum below that cutoff, and dominate every remaining prime by the candidate at 2.

   Preregistered escape witness: golden_upper_price_attained. It is consumed by the upper
   price specification, then by both directions of the public interval criterion. Removing
   it leaves no bound or extremum specification for the infinite next-layer value set;
   a supremum alternative would need a fresh boundedness proof, not merely binding the
   fixed-price criterion. Once boundedness is available, no epsilon argument is necessary.
   Companion edges (consumer -> prerequisite): upper-price specification -> attainment;
   interval criterion -> upper-price specification and positivity.
   Boundary convention: the source defines U only for n > 1. For empty prime support
   (n = 0 or 1), the real-valued API sets U(n) = L(n). This extends the existential criterion
   to n = 1; it does not describe all prices at n = 1 as a bounded interval. -/

namespace D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenPrimeLayerCofinite
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion

noncomputable section

private theorem marginal_pos {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < goldenLayerMarginal p a := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hiPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hiLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hden : 0 < 1 - (p : ℝ)⁻¹ ^ a :=
    sub_pos.mpr (pow_lt_one₀ hiPos.le hiLt (by omega))
  have hpow : (p : ℝ)⁻¹ ^ (a + 1) < (p : ℝ)⁻¹ ^ a :=
    pow_lt_pow_right_of_lt_one₀ hiPos hiLt (by omega)
  apply div_pos _ (Real.log_pos (by exact_mod_cast hp.one_lt))
  apply Real.log_pos
  exact (one_lt_div hden).mpr (by linarith)

/-- The best next layer is attained at a prime, despite ranging over all primes. -/
theorem golden_upper_price_attained {n : ℕ} (_hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ ∀ r : ℕ, r.Prime →
      goldenLayerMarginal r (n.factorization r + 1) ≤
        goldenLayerMarginal p (n.factorization p + 1) := by
  classical
  let f := fun p => goldenLayerMarginal p (n.factorization p + 1)
  have htwo : 0 < f 2 := marginal_pos Nat.prime_two (by omega)
  obtain ⟨P, hP⟩ := golden_layer_marginal_lt_of_prime_le htwo
  let primes := (Finset.range (max P 3)).filter Nat.Prime
  have htwoMem : 2 ∈ primes :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((by decide : 2 < 3).trans_le (Nat.le_max_right P 3)), Nat.prime_two⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image primes f ⟨2, htwoMem⟩
  refine ⟨p, (Finset.mem_filter.mp hp).2, fun r hr => ?_⟩
  by_cases hrP : r < max P 3
  · exact hmax r (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrP, hr⟩)
  · exact (hP r hr (by omega) (n.factorization r + 1) (by omega)).le.trans
      (hmax 2 htwoMem)

/-- L(n), the supremum of the next-layer prices, attained for positive n. -/
def goldenUpperPrice (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ p : ℕ, p.Prime ∧ x = goldenLayerMarginal p (n.factorization p + 1)}

/-- U(n), the minimum adopted-layer price; empty prime support is assigned L(n). -/
def goldenLowerPrice (n : ℕ) : ℝ := by
  classical
  exact if h : n.primeFactors.Nonempty then
    n.primeFactors.inf' h (fun p => goldenLayerMarginal p (n.factorization p))
  else goldenUpperPrice n

/-- Colossal abundance means global optimality at some positive resource price. -/
def IsColossallyAbundant (n : ℕ) : Prop :=
  ∃ lambda : ℝ, 0 < lambda ∧ IsGoldenResourceOptimal lambda n

/-- The upper price is a prime's next-layer value and bounds every next-layer value. -/
theorem golden_upper_price_spec {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧
      goldenUpperPrice n = goldenLayerMarginal p (n.factorization p + 1) ∧
      ∀ r : ℕ, r.Prime →
        goldenLayerMarginal r (n.factorization r + 1) ≤ goldenUpperPrice n := by
  obtain ⟨p, hp, hmax⟩ := golden_upper_price_attained hn
  have heq : goldenUpperPrice n = goldenLayerMarginal p (n.factorization p + 1) := by
    apply le_antisymm
    · exact csSup_le ⟨_, p, hp, rfl⟩ (by rintro x ⟨r, hr, rfl⟩; exact hmax r hr)
    · exact le_csSup ⟨_, by rintro x ⟨r, hr, rfl⟩; exact hmax r hr⟩ ⟨p, hp, rfl⟩
  exact ⟨p, hp, heq, fun r hr => heq ▸ hmax r hr⟩

/-- Every positive integer has a strictly positive upper layer price. -/
theorem golden_upper_price_pos {n : ℕ} (hn : 1 ≤ n) : 0 < goldenUpperPrice n := by
  obtain ⟨p, hp, heq, _⟩ := golden_upper_price_spec hn
  rw [heq]
  exact marginal_pos hp (by omega)

/-- A positive integer is colossally abundant exactly when its layer price interval is nonempty. -/
theorem colossally_abundant_iff_price_interval_nonempty {n : ℕ} (hn : 1 ≤ n) :
    IsColossallyAbundant n ↔ goldenUpperPrice n ≤ goldenLowerPrice n := by
  classical
  obtain ⟨p, hp, hupperEq, hupper⟩ := golden_upper_price_spec hn
  constructor
  · rintro ⟨lambda, hlambda, hopt⟩
    obtain ⟨hnext, hlast⟩ := (golden_resource_optimal_iff_layer_thresholds hlambda hn).mp hopt
    have hprice : goldenUpperPrice n ≤ lambda := hupperEq ▸ hnext p hp
    by_cases hs : n.primeFactors.Nonempty
    · rw [goldenLowerPrice, dif_pos hs]
      apply Finset.le_inf'
      intro r hr
      exact hprice.trans (hlast r (Nat.prime_of_mem_primeFactors hr)
        (Nat.dvd_of_mem_primeFactors hr))
    · simp only [goldenLowerPrice, dif_neg hs, le_refl]
  · intro hinterval
    refine ⟨goldenUpperPrice n, golden_upper_price_pos hn,
      (golden_resource_optimal_iff_layer_thresholds (golden_upper_price_pos hn) hn).mpr
        ⟨hupper, ?_⟩⟩
    intro r hr hrn
    have hmem := hr.mem_primeFactors hrn (show n ≠ 0 by omega)
    have hs : n.primeFactors.Nonempty := ⟨r, hmem⟩
    rw [goldenLowerPrice, dif_pos hs] at hinterval
    exact hinterval.trans (Finset.inf'_le _ hmem)

#print axioms golden_upper_price_attained
#print axioms colossally_abundant_iff_price_interval_nonempty

end

end D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval
