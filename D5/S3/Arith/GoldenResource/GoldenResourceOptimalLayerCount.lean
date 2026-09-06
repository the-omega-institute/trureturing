/- GID: D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive layer counts give an optimizer with minimal prime exponents. -/

import D5.S3.Arith.GoldenFutureExtensionMaximum
import D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
import Mathlib.Order.Interval.Set.Nat

/- Library-search audit trail (2026-09-07):
   1. This continuation repeated D5 searches for optimalLayerCount,
      positive_part_sum_finite_support, positive layers, layer count/prefix, colossally,
      and golden_resource_optimal: no public count characterization outside this draft.
      GoldenFutureExtensionMaximum has a private finite-prefix construction; its public
      golden_future_extension_maximum_attained is imported and applied at the integer 1.
      GoldenResourceThresholdCriterion supplies the public boundary-threshold equivalence.
      Both directly imported D5 modules have generality I (checked before writing this header).
   2. Pinned Mathlib v4.33.0 searches for goldenResource, goldenLayer, colossally,
      optimalLayerCount and positive_part_sum_finite_support had no hits. Searches for finite
      products, interval cardinalities, finite-set maxima and factorization reconstruction
      found Finset.exists_mem_eq_sup, Set.ncard_eq_toFinset_card, Nat.card_Icc,
      Nat.prod_pow_factorization_eq_self and Nat.factorization_le_iff_dvd; these are reused.
   3. Online Lean ecosystem search through NyxID/Tavily for "Lean formalization colossally
      abundant optimal prime exponent positive marginal layers" returned Wikipedia,
      MathWorld, Math StackExchange, a probability formalization, and Mathematics in Lean;
      no matching Lean declaration in those results. Request
      909c7e42-17bc-4ca5-a4c3-a2d8d769c13d. An initial HTTP 422 was corrected by supplying
      Content-Type: application/json; CLI exit zero alone did not establish HTTP success.
   4. The original preregistered witness positive_part_sum_finite_support is retained.
      Its finite union of factorization intervals bounds all active prime-layer pairs.
      Imported attainment alone does not identify those pairs or their cardinalities.
      The public count specification consumes the witness through its finite-support
      integer construction and positive_layers_eq_count_interval. The latter identifies
      a downward-closed finite layer set with the interval ending at its cardinality.
      These are arbitrary-price analytic/combinatorial results, not bounded computations
      or certified numerical instances. The predecessor's unverified audit was replaced
      by the continuation's own searches; its proof core is retained and kernel-checked.
   Scope: the minimal-exponent optimizer only. At equality other optimizers are allowed;
   no uniqueness of all optimizers and no positive-part supremum formula is asserted. -/

namespace D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenFutureExtensionMaximum
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion

noncomputable section

private theorem active_le_factorization {lambda : ℝ} (hlambda : 0 < lambda)
    {n p k : ℕ} (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal lambda n)
    (hp : p.Prime) (hgain : lambda < goldenLayerMarginal p k) :
    k ≤ n.factorization p := by
  have hnext := (golden_resource_optimal_iff_layer_thresholds hlambda hn).mp hopt |>.1 p hp
  by_contra h
  have hk : n.factorization p + 1 ≤ k := by omega
  rcases eq_or_lt_of_le hk with heq | hlt
  · rw [← heq] at hgain
    exact (not_lt_of_ge hnext) hgain
  · exact (not_lt_of_ge ((golden_layer_strict_decrease hp (by omega) hlt).le.trans
      hnext)) hgain

/-- The set of all strictly profitable positive prime layers is finite. -/
theorem positive_part_sum_finite_support {lambda : ℝ} (hlambda : 0 < lambda) :
    {pk : ℕ × ℕ | 1 ≤ pk.2 ∧ pk.1.Prime ∧
      lambda < goldenLayerMarginal pk.1 pk.2}.Finite := by
  classical
  obtain ⟨n, _, hn, hmax⟩ :=
    golden_future_extension_maximum_attained hlambda (n := 1) le_rfl
  have hopt : IsGoldenResourceOptimal lambda n := by
    intro m hm
    exact (sub_le_sub_iff_right _).mp (hmax m (one_dvd m) hm)
  let layers := n.primeFactors.biUnion fun p => (Icc 1 (n.factorization p)).image (p, ·)
  apply layers.finite_toSet.subset
  rintro ⟨p, k⟩ ⟨hk, hp, hgain⟩
  have hle := active_le_factorization hlambda hn hopt hp hgain
  change k ≤ n.factorization p at hle
  change 1 ≤ k at hk
  have hmem : p ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  exact mem_biUnion.mpr ⟨p, hmem, mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk, hle⟩, rfl⟩⟩

/-- The number of strictly profitable positive layers, zero for nonprime directions. -/
def optimalLayerCount (lambda : ℝ) (p : ℕ) : ℕ :=
  {k : ℕ | 1 ≤ k ∧ p.Prime ∧ lambda < goldenLayerMarginal p k}.ncard

private theorem positive_layers_finite {lambda : ℝ} (hlambda : 0 < lambda) (p : ℕ) :
    {k : ℕ | 1 ≤ k ∧ p.Prime ∧ lambda < goldenLayerMarginal p k}.Finite := by
  exact (positive_part_sum_finite_support hlambda).preimage
    (fun _ _ _ _ h => (Prod.mk.inj h).2)

/-- Every prime's active layers form the initial interval ending at their cardinality. -/
theorem positive_layers_eq_count_interval {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) :
    {k : ℕ | 1 ≤ k ∧ p.Prime ∧ lambda < goldenLayerMarginal p k} =
      Set.Icc 1 (optimalLayerCount lambda p) := by
  classical
  let hfinite := positive_layers_finite hlambda p
  let s := hfinite.toFinset
  let a := s.sup id
  have hmem (k : ℕ) : k ∈ s ↔ 1 ≤ k ∧ p.Prime ∧
      lambda < goldenLayerMarginal p k := by simp [s]
  have hs : s = Icc 1 a := by
    ext k
    constructor
    · intro hk
      exact mem_Icc.mpr ⟨(hmem k).mp hk |>.1, le_sup (f := id) hk⟩
    · intro hk
      obtain ⟨hk, hka⟩ := mem_Icc.mp hk
      have hne : s.Nonempty := by
        by_contra h
        have hz : a = 0 := by simp [a, not_nonempty_iff_eq_empty.mp h]
        omega
      obtain ⟨b, hb, hab⟩ := exists_mem_eq_sup s hne id
      have hba : b = a := hab.symm
      have hgain := (hmem b).mp hb |>.2.2
      rw [hba] at hgain
      apply (hmem k).mpr
      refine ⟨hk, hp, ?_⟩
      rcases eq_or_lt_of_le hka with rfl | hlt
      · exact hgain
      · exact hgain.trans (golden_layer_strict_decrease hp hk hlt)
  have hcount : optimalLayerCount lambda p = a := by
    rw [optimalLayerCount, Set.ncard_eq_toFinset_card _ hfinite]
    change s.card = a
    rw [hs, Nat.card_Icc]
    omega
  rw [hcount]
  ext k
  change (1 ≤ k ∧ p.Prime ∧ lambda < goldenLayerMarginal p k) ↔ _
  rw [← hmem k, hs]
  simp

private theorem count_eq_zero_of_not_prime (lambda : ℝ) {p : ℕ} (hp : ¬p.Prime) :
    optimalLayerCount lambda p = 0 := by
  simp [optimalLayerCount, hp]

private theorem count_layer_active {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) (ha : 1 ≤ optimalLayerCount lambda p) :
    lambda < goldenLayerMarginal p (optimalLayerCount lambda p) := by
  have hmem : optimalLayerCount lambda p ∈
      {k : ℕ | 1 ≤ k ∧ p.Prime ∧ lambda < goldenLayerMarginal p k} := by
    rw [positive_layers_eq_count_interval hlambda hp]
    exact ⟨ha, le_rfl⟩
  exact hmem.2.2

private theorem count_next_layer_le {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p (optimalLayerCount lambda p + 1) ≤ lambda := by
  apply le_of_not_gt
  intro hgain
  have hmem : optimalLayerCount lambda p + 1 ∈
      {k : ℕ | 1 ≤ k ∧ p.Prime ∧ lambda < goldenLayerMarginal p k} :=
    ⟨by omega, hp, hgain⟩
  rw [positive_layers_eq_count_interval hlambda hp] at hmem
  exact Nat.not_succ_le_self _ hmem.2

/-- Strictly profitable layer counts are realized simultaneously by a positive optimizer
that divides every positive optimizer, hence has the smallest possible prime exponents. -/
theorem optimal_layer_count_spec {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ n : ℕ, 1 ≤ n ∧
      (∀ p : ℕ, n.factorization p = optimalLayerCount lambda p) ∧
      IsGoldenResourceOptimal lambda n ∧
      ∀ m : ℕ, 1 ≤ m → IsGoldenResourceOptimal lambda m → n ∣ m := by
  classical
  let layers := (positive_part_sum_finite_support hlambda).toFinset
  let support := layers.image Prod.fst
  have count_support : ∀ p, optimalLayerCount lambda p ≠ 0 → p ∈ support := by
    intro p ha
    have hp : p.Prime := by
      by_contra h
      exact ha (count_eq_zero_of_not_prime lambda h)
    have ha1 : 1 ≤ optimalLayerCount lambda p := Nat.one_le_iff_ne_zero.mpr ha
    have hactive : (p, optimalLayerCount lambda p) ∈ layers := by
      exact ((positive_part_sum_finite_support hlambda).mem_toFinset).mpr
        ⟨ha1, hp, count_layer_active hlambda hp ha1⟩
    exact mem_image.mpr ⟨(p, optimalLayerCount lambda p), hactive, rfl⟩
  let target : ℕ →₀ ℕ := Finsupp.onFinset support (optimalLayerCount lambda) count_support
  let n := target.prod (· ^ ·)
  have target_prime : ∀ p ∈ target.support, p.Prime := by
    intro p hp
    have hpSupport : p ∈ support := Finsupp.support_onFinset_subset hp
    obtain ⟨pk, hpk, rfl⟩ := mem_image.mp hpSupport
    exact (((positive_part_sum_finite_support hlambda).mem_toFinset).mp hpk).2.1
  have hfactorization : n.factorization = target :=
    Nat.prod_pow_factorization_eq_self target_prime
  have hn0 : n ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (target_prime p hp).ne_zero
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hcounts (p : ℕ) : n.factorization p = optimalLayerCount lambda p := by
    rw [hfactorization]
    rfl
  refine ⟨n, hn, hcounts, ?_, ?_⟩
  · apply (golden_resource_optimal_iff_layer_thresholds hlambda hn).mpr
    constructor
    · intro p hp
      rw [hcounts]
      exact count_next_layer_le hlambda hp
    · intro p hp hpn
      have ha : 1 ≤ optimalLayerCount lambda p := by
        rw [← hcounts]
        exact hp.factorization_pos_of_dvd hn0 hpn
      rw [hcounts]
      exact (count_layer_active hlambda hp ha).le
  · intro m hm hopt
    apply (Nat.factorization_le_iff_dvd hn0 (by omega)).mp
    intro p
    rw [hcounts]
    by_cases hp : p.Prime
    · by_cases ha : optimalLayerCount lambda p = 0
      · simp [ha]
      · exact active_le_factorization hlambda hm hopt hp
          (count_layer_active hlambda hp (Nat.one_le_iff_ne_zero.mpr ha))
    · rw [count_eq_zero_of_not_prime lambda hp]
      exact Nat.zero_le _

#print axioms positive_part_sum_finite_support
#print axioms positive_layers_eq_count_interval
#print axioms optimal_layer_count_spec

end

end D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
