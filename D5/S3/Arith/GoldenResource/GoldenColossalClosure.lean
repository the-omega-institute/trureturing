/- GID: D5/S3/Arith/GoldenResource/GoldenColossalClosure
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenColossalClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The threshold closure divides every colossally abundant multiple of its base. -/

import D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval

/- Library-search audit trail (2026-09-07):
   1. D5 searches for colossalClosure, goldenPriceThreshold, support_price_le_threshold,
      colossally, and goldenLayerMarginal found no closure or cross-integer price theorem.
      GoldenResourcePriceInterval was located in existing commits 4c4aedf8cf/211533ac45
      and brought into this lane unchanged. Its generality header is I. Its definitions,
      the frozen fixed-price criterion, strict marginal decrease, layer decay, and uniform
      prime cutoff are reused directly. GoldenFutureExtensionMaximum only exports an
      objective-maximizing multiple, without minimality or its private layer construction.
      The existing marginal-positivity proofs are private, not a public importable API.
   2. Pinned Mathlib v4.33.0: searches for colossal, colossally, colossalClosure,
      support_price_le_threshold, and goldenLowerPrice found no specialized declaration.
      Nat.factorization_le_iff_dvd, Nat.prod_pow_factorization_eq_self,
      Nat.prod_pow_dvd_of_le_factorization, Nat.nonempty_primeFactors, Finset.le_inf',
      Finset.inf'_le, and Nat.find_min' supply the generic components used here.
   3. Third-party Lean ecosystem via NyxID/Tavily: queries "Lean theorem prover colossally
      abundant closure divisibility goldenLayerMarginal" and "colossally abundant Lean
      formalization closure" returned generic Lean resources and informal abundance
      descriptions, with no matching Lean declaration in the returned results. The initial
      request without a content-type header returned HTTP 422 and is not counted as a search.
   4. The new construction joins the base exponents with strict-positive layer prefixes.

   Escape preregistration v2, recorded in the attempt artifact before implementation:
   support_price_le_threshold requires 1 <= N, because the frozen abundance definition
   does not assert positivity. The final divisibility theorem handles N = 0 separately.
   The witness relates the support price of N to the adopted layers of B; its bound is
   consumed to bound every strict-positive prefix by the corresponding exponent of N.
   Without that relation, the fixed-price criterion leaves the two prices unrelated.
   This is an arbitrary-input analytic construction, not a finite certified instance.
   Companion edges (consumer -> prerequisite): closure divisibility -> support price bound;
   closure abundance -> threshold positivity and strict-positive prefix construction. -/

namespace D5.S3.Arith.GoldenResource.GoldenColossalClosure

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenPrimeLayerCofinite
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval

noncomputable section

/-- The largest price compatible with retaining every layer of the base. -/
def goldenPriceThreshold (B : ℕ) : ℝ := goldenLowerPrice B

private theorem marginal_pos {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < goldenLayerMarginal p a := by
  have hiPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hiLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hden : 0 < 1 - (p : ℝ)⁻¹ ^ a :=
    sub_pos.mpr (pow_lt_one₀ hiPos.le hiLt (by omega))
  have hpow : (p : ℝ)⁻¹ ^ (a + 1) < (p : ℝ)⁻¹ ^ a :=
    pow_lt_pow_right_of_lt_one₀ hiPos hiLt (by omega)
  apply div_pos _ (Real.log_pos (by exact_mod_cast hp.one_lt))
  apply Real.log_pos
  exact (one_lt_div hden).mpr (by linarith)

private theorem threshold_pos {B : ℕ} (hB : 1 < B) : 0 < goldenPriceThreshold B := by
  classical
  rw [goldenPriceThreshold, goldenLowerPrice, dif_pos (Nat.nonempty_primeFactors.mpr hB)]
  apply (Finset.lt_inf'_iff _).mpr
  intro p hp
  apply marginal_pos (Nat.prime_of_mem_primeFactors hp)
  have hne : B.factorization p ≠ 0 := by
    simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
  omega

private theorem threshold_le_layer {B p : ℕ} (hB : 1 < B) (hp : p.Prime)
    (hpdvd : p ∣ B) : goldenPriceThreshold B ≤ goldenLayerMarginal p (B.factorization p) := by
  classical
  rw [goldenPriceThreshold, goldenLowerPrice, dif_pos (Nat.nonempty_primeFactors.mpr hB)]
  exact Finset.inf'_le _ (hp.mem_primeFactors hpdvd (by omega))

/-- A positive abundant multiple's supporting price is bounded by the base threshold. -/
theorem support_price_le_threshold {B N : ℕ} (hB : 1 < B) (hn : 1 ≤ N)
    (hdvd : B ∣ N) (_hN : IsColossallyAbundant N) :
    ∀ lambda : ℝ, 0 < lambda → IsGoldenResourceOptimal lambda N →
      lambda ≤ goldenPriceThreshold B := by
  classical
  intro lambda hlambda hopt
  have hlast := (golden_resource_optimal_iff_layer_thresholds hlambda hn).mp hopt |>.2
  have hfac := (Nat.factorization_le_iff_dvd (by omega : B ≠ 0)
    (by omega : N ≠ 0)).mpr hdvd
  rw [goldenPriceThreshold, goldenLowerPrice, dif_pos (Nat.nonempty_primeFactors.mpr hB)]
  apply Finset.le_inf'
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hbase : 1 ≤ B.factorization p := by
    have hne : B.factorization p ≠ 0 := by
      simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
    omega
  have hprice := hlast p hprime ((Nat.dvd_of_mem_primeFactors hp).trans hdvd)
  rcases eq_or_lt_of_le (hfac p) with heq | hlt
  · simpa only [heq] using hprice
  · exact hprice.trans (golden_layer_strict_decrease hprime hbase hlt).le

private def strictLayerCount (lambda : ℝ) (p : ℕ) : ℕ := by
  classical
  exact if h : ∃ a : ℕ, goldenLayerMarginal p (a + 1) ≤ lambda then Nat.find h else 0

private theorem layer_cutoff_exists {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) : ∃ a : ℕ, goldenLayerMarginal p (a + 1) ≤ lambda := by
  obtain ⟨a, ha⟩ := golden_layer_marginal_lt_of_le hp hlambda
  exact ⟨a, (ha (a + 1) (by omega)).le⟩

private theorem count_next_le {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p (strictLayerCount lambda p + 1) ≤ lambda := by
  classical
  rw [strictLayerCount, dif_pos (layer_cutoff_exists hlambda hp)]
  exact Nat.find_spec (layer_cutoff_exists hlambda hp)

private theorem count_le_of_next_le {lambda : ℝ} {p a : ℕ}
    (ha : goldenLayerMarginal p (a + 1) ≤ lambda) : strictLayerCount lambda p ≤ a := by
  classical
  rw [strictLayerCount, dif_pos ⟨a, ha⟩]
  exact Nat.find_min' _ ha

private theorem layer_gt_of_le_count {lambda : ℝ} (hlambda : 0 < lambda)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hac : a ≤ strictLayerCount lambda p) :
    lambda < goldenLayerMarginal p a := by
  classical
  rw [strictLayerCount, dif_pos (layer_cutoff_exists hlambda hp)] at hac
  have h := Nat.find_min (layer_cutoff_exists hlambda hp)
    (show a - 1 < Nat.find (layer_cutoff_exists hlambda hp) by omega)
  simpa only [Nat.sub_add_cancel ha] using lt_of_not_ge h

end

end D5.S3.Arith.GoldenResource.GoldenColossalClosure
