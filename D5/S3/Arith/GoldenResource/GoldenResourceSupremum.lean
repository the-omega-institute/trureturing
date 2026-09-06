/- GID: D5/S3/Arith/GoldenResource/GoldenResourceSupremum
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResourceSupremum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: At positive prices the resource supremum is the finite sum of positive layer gains. -/

import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Arith.GoldenResourceObjectiveFactorization

/- Library-search audit trail (2026-09-07):
   1. This continuation repeated D5 searches for golden_resource_supremum,
      objective_at_optimal, local_objective/sum, goldenResourceObjective,
      goldenLayerMarginal, colossally, superabundant and positive_part: no public
      supremum formula or local telescoping sum outside this draft. Direct imports above
      all have generality I, checked before editing.
      Reused: optimal_layer_count_spec, positive_part_sum_finite_support,
      positive_layers_eq_count_interval, golden_resource_objective_factorization,
      golden_resource_objective_sum_on and golden_resource_objective_single_layer_delta.
      The public single-layer delta avoids repeating the private logarithmic difference
      proofs in GoldenLocalThreshold and GoldenResourceThresholdCriterion.
   2. Pinned Mathlib v4.33.0 searches for goldenResource, goldenLayer, colossally,
      superabundant and objective_at_optimal had no hits. Finite-sum and supremum searches
      found Finset.sum_Icc_succ_top, Finset.sum_range_sub, Finset.sum_fiberwise_of_maps_to,
      Finset.sum_bij and IsGreatest.csSup_eq; the applicable general APIs are reused below.
   3. Online Lean ecosystem search via NyxID/Tavily for "Lean formalization colossally
      abundant supremum positive marginal layers goldenResourceObjective" returned ordinary
      colossally abundant number references (Wikipedia, HandWiki, en-academic), no matching
      Lean declaration. This continuation's request: a73ca8f7-1bb6-4e8c-aaff-bdb4a4ef984c.
      A second query, "colossally abundant Lean formalization", returned Wikipedia,
      MathWorld, MathOverflow, lean-lang.org and Mathematics in Lean, with no matching
      declaration. Request: 9e5bee73-27fe-4bd5-b886-a7f25d1eb5d2.
   4. Preregistered witness: objective_at_optimal_eq_positive_part_sum. It evaluates any
      positive integer realizing optimalLayerCount, hence applies to the integer supplied
      by optimal_layer_count_spec. The live bridge telescopes prime-power increments and
      identifies every active pair with a factorization interval before regrouping the sum.
      Frozen optimality alone gives no value; frozen factorization alone gives no layer sum.
      The right side is a Finset.sum on the full finite strict-gain set. Outside this set,
      every prime's positive-index layer has zero positive part. No assertion is made at
      nonpositive prices. The predecessor's proof core is retained for kernel verification;
      the audit above records this continuation's own searches.
      Companion edges: supremum -> objective_at_optimal_eq_positive_part_sum;
      equality-price invariance -> imported single-layer delta. The latter is the named
      equality-price clause accompanying the supremum formula, and is bind-only.
      Admission basis: escape-witness. Computational content: none (arbitrary real prices,
      arbitrary integers and primes; no numerical instance or bounded computation). -/

namespace D5.S3.Arith.GoldenResource.GoldenResourceSupremum

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison

noncomputable section

private theorem local_eq_prime_power (lambda : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective lambda p a = goldenResourceObjective lambda (p ^ a) := by
  have hn : 1 ≤ p ^ a := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  rw [golden_resource_objective_sum_on lambda hn {p} (by
    intro q hq
    exact mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq
      (Nat.prime_of_mem_primeFactors hq) hp).mp
        ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))))]
  simp [hp.factorization_pow]

private theorem local_eq_layer_sum (lambda : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective lambda p a =
      ∑ k ∈ Icc 1 a, Real.log p * (goldenLayerMarginal p k - lambda) := by
  induction a with
  | zero =>
      by_cases h : (p : ℝ)⁻¹ = 1 <;> simp [goldenPrimeLocalObjective, h]
  | succ a ih =>
      rw [sum_Icc_succ_top (by omega), ← ih]
      have h := golden_resource_objective_single_layer_delta lambda
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero a hp.ne_zero)) hp
      rw [← pow_succ, ← local_eq_prime_power lambda hp,
        ← local_eq_prime_power lambda hp] at h
      simp only [hp.factorization_pow, Finsupp.single_eq_same] at h
      linarith [h]

/-- At the minimal-count configuration the objective equals all strictly positive gains. -/
theorem objective_at_optimal_eq_positive_part_sum {lambda : ℝ} (hlambda : 0 < lambda)
    {n : ℕ} (hn : 1 ≤ n)
    (hcounts : ∀ p : ℕ, n.factorization p = optimalLayerCount lambda p) :
    goldenResourceObjective lambda n =
      ∑ pk ∈ (positive_part_sum_finite_support hlambda).toFinset,
        Real.log pk.1 * (goldenLayerMarginal pk.1 pk.2 - lambda) := by
  classical
  let layers := (positive_part_sum_finite_support hlambda).toFinset
  have hmem (p k : ℕ) : (p, k) ∈ layers ↔
      1 ≤ k ∧ p.Prime ∧ k ≤ n.factorization p := by
    simp only [layers, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    by_cases hp : p.Prime
    · have hi := Set.ext_iff.mp (positive_layers_eq_count_interval hlambda hp) k
      simp only [Set.mem_ofPred_eq, Set.mem_Icc, ← hcounts p] at hi
      tauto
    · simp [hp]
  have hmaps : ∀ pk ∈ layers, pk.1 ∈ n.primeFactors := by
    rintro ⟨p, k⟩ hpk
    have h := (hmem p k).mp hpk
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < k) h.2.2)
  change goldenResourceObjective lambda n =
    ∑ pk ∈ layers, Real.log pk.1 * (goldenLayerMarginal pk.1 pk.2 - lambda)
  rw [golden_resource_objective_factorization lambda hn,
    ← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [local_eq_layer_sum lambda hprime]
  apply sum_bij (fun k _ => (p, k))
  · intro k hk
    exact mem_filter.mpr ⟨(hmem p k).mpr
      ⟨(mem_Icc.mp hk).1, hprime, (mem_Icc.mp hk).2⟩, rfl⟩
  · intro a _ b _ hab
    exact (Prod.mk.inj hab).2
  · rintro ⟨q, k⟩ hqk
    obtain ⟨hactive, hqp⟩ := mem_filter.mp hqk
    change q = p at hqp
    subst q
    exact ⟨k, mem_Icc.mpr ⟨((hmem p k).mp hactive).1,
      ((hmem p k).mp hactive).2.2⟩, rfl⟩
  · intro k _
    rfl

/-- The supremum over positive integers is the finite sum of all positive prime-layer gains. -/
theorem golden_resource_supremum_eq_positive_part_sum {lambda : ℝ}
    (hlambda : 0 < lambda) :
    sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ goldenResourceObjective lambda n = x} =
      ∑ pk ∈ (positive_part_sum_finite_support hlambda).toFinset,
        Real.log pk.1 * (goldenLayerMarginal pk.1 pk.2 - lambda) := by
  obtain ⟨n, hn, hcounts, hopt, _⟩ := optimal_layer_count_spec hlambda
  have hgreatest : IsGreatest
      {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ goldenResourceObjective lambda m = x}
      (goldenResourceObjective lambda n) := by
    refine ⟨⟨n, hn, rfl⟩, ?_⟩
    rintro x ⟨m, hm, rfl⟩
    exact hopt m hm
  rw [hgreatest.csSup_eq]
  exact objective_at_optimal_eq_positive_part_sum hlambda hn hcounts

/-- Adding or removing an equality-price layer leaves the objective unchanged. -/
theorem golden_resource_objective_eq_of_layer_price (lambda : ℝ) {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime)
    (hprice : goldenLayerMarginal p (n.factorization p + 1) = lambda) :
    goldenResourceObjective lambda (n * p) = goldenResourceObjective lambda n := by
  have h := golden_resource_objective_single_layer_delta lambda hn hp
  rw [hprice, sub_self, zero_mul] at h
  exact sub_eq_zero.mp h

end

#print axioms objective_at_optimal_eq_positive_part_sum
#print axioms golden_resource_supremum_eq_positive_part_sum
#print axioms golden_resource_objective_eq_of_layer_price

end D5.S3.Arith.GoldenResource.GoldenResourceSupremum
