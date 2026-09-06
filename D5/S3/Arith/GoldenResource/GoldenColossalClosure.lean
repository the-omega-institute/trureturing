/- GID: D5/S3/Arith/GoldenResource/GoldenColossalClosure
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenColossalClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The threshold closure divides every colossally abundant multiple of its base. -/

import D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval
import Mathlib.Order.Interval.Set.Nat

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

private theorem positive_layers_eq_interval {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) :
    {a : ℕ | 1 ≤ a ∧ lambda < goldenLayerMarginal p a} =
      Set.Icc 1 (strictLayerCount lambda p) := by
  ext a
  constructor
  · rintro ⟨ha, hgain⟩
    refine ⟨ha, ?_⟩
    by_contra hnot
    have hle : strictLayerCount lambda p + 1 ≤ a := by omega
    have hnext := count_next_le hlambda hp
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hnext
      exact (not_lt_of_ge hnext) hgain
    · exact (not_lt_of_ge
        ((golden_layer_strict_decrease hp (by omega) hlt).le.trans hnext)) hgain
  · rintro ⟨ha, hac⟩
    exact ⟨ha, layer_gt_of_le_count hlambda hp ha hac⟩

/-- The number of positive prime layers strictly more valuable than the base threshold. -/
def goldenPositiveLayerCount (B p : ℕ) : ℕ :=
  {a : ℕ | 1 ≤ a ∧ goldenPriceThreshold B < goldenLayerMarginal p a}.ncard

private theorem positive_count_eq {B p : ℕ} (hB : 1 < B) (hp : p.Prime) :
    goldenPositiveLayerCount B p = strictLayerCount (goldenPriceThreshold B) p := by
  rw [goldenPositiveLayerCount, positive_layers_eq_interval (threshold_pos hB) hp,
    Set.ncard_Icc_nat]
  omega

private def closureExponent (B p : ℕ) : ℕ :=
  if p.Prime then max (B.factorization p) (strictLayerCount (goldenPriceThreshold B) p) else 0

private theorem closure_exponents_exist {B : ℕ} (hB : 1 < B) :
    ∃ f : ℕ →₀ ℕ, ∀ p, f p = closureExponent B p := by
  classical
  obtain ⟨P, hP⟩ := golden_layer_marginal_lt_of_prime_le (threshold_pos hB)
  let support := B.primeFactors ∪ Finset.range P
  have hs : ∀ p, closureExponent B p ≠ 0 → p ∈ support := by
    intro p hne
    by_cases hp : p.Prime
    · by_cases hmem : p ∈ B.primeFactors
      · exact Finset.mem_union_left _ hmem
      · apply Finset.mem_union_right
        apply Finset.mem_range.mpr
        by_contra hnot
        have hcount : strictLayerCount (goldenPriceThreshold B) p = 0 :=
          Nat.eq_zero_of_le_zero (count_le_of_next_le
            (hP p hp (by omega) 1 (by omega)).le)
        have hbase : B.factorization p = 0 := by
          simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hmem
        exact hne (by simp [closureExponent, hp, hcount, hbase])
    · exact (hne (by simp [closureExponent, hp])).elim
  exact ⟨Finsupp.onFinset support (closureExponent B) hs, fun _ => rfl⟩

private def closureFactors (B : ℕ) : ℕ →₀ ℕ :=
  if hB : 1 < B then (closure_exponents_exist hB).choose else B.factorization

private theorem factors_apply {B : ℕ} (hB : 1 < B) (p : ℕ) :
    closureFactors B p = closureExponent B p := by
  rw [closureFactors, dif_pos hB]
  exact (closure_exponents_exist hB).choose_spec p

private theorem factors_prime {B : ℕ} (hB : 1 < B) :
    ∀ p ∈ (closureFactors B).support, p.Prime := by
  intro p hp
  by_contra hnot
  have heq : closureFactors B p = 0 := by
    rw [factors_apply hB, closureExponent, if_neg hnot]
  exact (Finsupp.mem_support_iff.mp hp) heq

/-- The finite prime product with exponent max(base exponent, strict-positive layer count).
For the out-of-source boundary inputs zero and one, the closure is the input itself. -/
def colossalClosure (B : ℕ) : ℕ :=
  if 1 < B then (closureFactors B).prod (· ^ ·) else B

private theorem closure_pos {B : ℕ} (hB : 1 < B) : 1 ≤ colossalClosure B := by
  rw [colossalClosure, if_pos hB]
  apply Nat.one_le_iff_ne_zero.mpr
  apply Finsupp.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (factors_prime hB p hp).ne_zero

private theorem closure_factorization {B : ℕ} (hB : 1 < B) :
    (colossalClosure B).factorization = closureFactors B := by
  rw [colossalClosure, if_pos hB]
  exact Nat.prod_pow_factorization_eq_self (factors_prime hB)

/-- The constructed integer has exactly the exponents in the threshold-count formula. -/
theorem colossal_closure_factorization {B p : ℕ} (hB : 1 < B) (hp : p.Prime) :
    (colossalClosure B).factorization p =
      max (B.factorization p) (goldenPositiveLayerCount B p) := by
  rw [closure_factorization hB, factors_apply hB, closureExponent, if_pos hp,
    positive_count_eq hB hp]

/-- The threshold closure retains all factors required by its base. -/
theorem dvd_colossal_closure {B : ℕ} (hB : 1 < B) : B ∣ colossalClosure B := by
  rw [colossalClosure, if_pos hB]
  apply Nat.dvd_prod_pow_of_factorization_le (by omega : B ≠ 0)
  intro p
  rw [factors_apply hB, closureExponent]
  by_cases hp : p.Prime
  · rw [if_pos hp]
    exact Nat.le_max_left _ _
  · simp [hp, Nat.factorization_eq_zero_of_not_prime B hp]

/-- Every colossally abundant multiple of the base contains its threshold closure. -/
theorem colossal_closure_dvd_of_dvd_colossally_abundant
    {B N : ℕ} (hB : 1 < B) (hN : IsColossallyAbundant N) (hdvd : B ∣ N) :
    colossalClosure B ∣ N := by
  by_cases hzero : N = 0
  · rw [hzero]
    exact dvd_zero _
  have hn : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hzero
  obtain ⟨lambda, hlambda, hopt⟩ := hN
  have hprice := support_price_le_threshold hB hn hdvd ⟨lambda, hlambda, hopt⟩
    lambda hlambda hopt
  have hnext := (golden_resource_optimal_iff_layer_thresholds hlambda hn).mp hopt |>.1
  have hfac := (Nat.factorization_le_iff_dvd (by omega : B ≠ 0) hzero).mpr hdvd
  rw [colossalClosure, if_pos hB]
  apply Nat.prod_pow_dvd_of_le_factorization
  intro p
  rw [factors_apply hB, closureExponent]
  by_cases hp : p.Prime
  · rw [if_pos hp]
    exact max_le (hfac p) (count_le_of_next_le ((hnext p hp).trans hprice))
  · simp [hp]

/-- The threshold closure itself is colossally abundant, including at tied layer prices. -/
theorem colossal_closure_is_colossally_abundant {B : ℕ} (hB : 1 < B) :
    IsColossallyAbundant (colossalClosure B) := by
  have hpos := threshold_pos hB
  refine ⟨goldenPriceThreshold B, hpos,
    (golden_resource_optimal_iff_layer_thresholds hpos (closure_pos hB)).mpr ⟨?_, ?_⟩⟩
  · intro p hp
    rw [closure_factorization hB, factors_apply hB, closureExponent, if_pos hp]
    have hnext := count_next_le hpos hp
    rcases eq_or_lt_of_le
      (Nat.le_max_right (B.factorization p) (strictLayerCount (goldenPriceThreshold B) p))
      with heq | hlt
    · simpa only [← heq] using hnext
    · exact (golden_layer_strict_decrease hp (by omega)
        (Nat.add_lt_add_right hlt 1)).le.trans hnext
  · intro p hp hpdvd
    have hactive : 1 ≤ (colossalClosure B).factorization p := by
      have hmem := hp.mem_primeFactors hpdvd
        (Nat.ne_zero_of_lt (closure_pos hB))
      have hne : (colossalClosure B).factorization p ≠ 0 := by
        simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hmem
      omega
    rw [closure_factorization hB, factors_apply hB, closureExponent, if_pos hp] at hactive ⊢
    by_cases hle : strictLayerCount (goldenPriceThreshold B) p ≤ B.factorization p
    · rw [max_eq_left hle] at hactive ⊢
      have hbaseDvd : p ∣ B := by
        apply Nat.dvd_of_mem_primeFactors
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        omega
      exact threshold_le_layer hB hp hbaseDvd
    · have hle' : B.factorization p ≤ strictLayerCount (goldenPriceThreshold B) p := by omega
      rw [max_eq_right hle'] at hactive ⊢
      exact (layer_gt_of_le_count hpos hp hactive le_rfl).le

#print axioms support_price_le_threshold
#print axioms colossal_closure_dvd_of_dvd_colossally_abundant
#print axioms colossal_closure_is_colossally_abundant

end

end D5.S3.Arith.GoldenResource.GoldenColossalClosure
