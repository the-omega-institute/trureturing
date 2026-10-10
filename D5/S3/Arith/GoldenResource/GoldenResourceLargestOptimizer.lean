/- GID: D5/S3/Arith/GoldenResource/GoldenResourceLargestOptimizer
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResourceLargestOptimizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct the full largest CA optimizer and its exact inclusive-layer log clock. -/

import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount

/- Repo-prior-exposed: the strict minimal-count construction, arbitrary-optimizer
   threshold criterion, pressure formula, local thresholds, marginal decay,
   prime-cofinite cutoff and future-maximum construction were read at immutable
   dev f3c5712f662d169833ab6e5830c5a32df1f1c2d5. They are reused, not new results.
   The preregistered missing arithmetic step is the equality-inclusive product,
   its actual factorization and maximality, consumed in the full-layer log clock.
   Search: all D5 and adjacent Blueprint, including private proofs, have no
   inclusive largest optimizer or its log increment. Pinned Mathlib supplies
   Nat.factorization_prod, prime factorizations, Finset.prod_sdiff and Real.log_prod.
   Public Loogle queries for colossally/abundant/goldenLayerMarginal found no
   specialized declaration; this is bounded search, not originality certification.
   No nonpositive-price optimizer, inverse event roots, sampling rate, prime-span
   estimate, signed Robin estimate or RH conclusion is asserted.
   Admission basis: escape-witness; arbitrary-price arithmetic construction.
   Helpers are consumed by largest_ca_spec and largest_ca_clock, not independent
   new-content claims. Both public results have a live path through the product's
   factorization; the clock also uses its literal finite product definition. -/

namespace D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion

noncomputable section

private theorem full_layer_support_finite {lambda : ℝ} (hlambda : 0 < lambda) :
    {pk : ℕ × ℕ | 1 ≤ pk.2 ∧ pk.1.Prime ∧
      lambda ≤ goldenLayerMarginal pk.1 pk.2}.Finite := by
  apply (positive_part_sum_finite_support (show 0 < lambda / 2 by linarith)).subset
  intro pk hpk
  exact ⟨hpk.1, hpk.2.1, lt_of_lt_of_le (by linarith) hpk.2.2⟩

/-- All adopted layers, including every equality-price layer at every prime.
The nonpositive-price branch is only a total-definition convention. -/
def fullCALayers (lambda : ℝ) : Finset (ℕ × ℕ) :=
  if h : 0 < lambda then (full_layer_support_finite h).toFinset else ∅

/-- Inclusive prime exponents; nonprime directions have zero count. -/
def fullCALayerCount (lambda : ℝ) (p : ℕ) : ℕ :=
  ((fullCALayers lambda).filter fun pk => pk.1 = p).card

/-- The actual positive integer obtained by multiplying one prime per adopted layer. -/
def largestCA (lambda : ℝ) : ℕ := ∏ pk ∈ fullCALayers lambda, pk.1

private theorem mem_full_layers {lambda : ℝ} (hlambda : 0 < lambda) (p k : ℕ) :
    (p, k) ∈ fullCALayers lambda ↔
      1 ≤ k ∧ p.Prime ∧ lambda ≤ goldenLayerMarginal p k := by
  simp [fullCALayers, dif_pos hlambda]

private theorem full_layer_prime (lambda : ℝ) {pk : ℕ × ℕ}
    (hpk : pk ∈ fullCALayers lambda) : pk.1.Prime := by
  by_cases h : 0 < lambda
  · exact ((mem_full_layers h pk.1 pk.2).mp hpk).2.1
  · simp [fullCALayers, h] at hpk

private theorem nonprime_count (lambda : ℝ) {p : ℕ} (hp : ¬p.Prime) :
    fullCALayerCount lambda p = 0 := by
  have hempty : (fullCALayers lambda).filter (fun pk => pk.1 = p) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro pk hpk heq
    exact hp (heq ▸ full_layer_prime lambda hpk)
  simp [fullCALayerCount, hempty]

private theorem full_count_interval {lambda : ℝ} (hlambda : 0 < lambda)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p, k) ∈ fullCALayers lambda ↔ 1 ≤ k ∧ k ≤ fullCALayerCount lambda p := by
  classical
  let s := (fullCALayers lambda).filter fun pk => pk.1 = p
  let a := s.sup Prod.snd
  have hmem (j : ℕ) : (p, j) ∈ s ↔ (p, j) ∈ fullCALayers lambda := by
    simp [s]
  have hs : s = (Icc 1 a).image (p, ·) := by
    ext pk
    constructor
    · intro hpk
      obtain ⟨hpk', heq⟩ := mem_filter.mp hpk
      have hk := ((mem_full_layers hlambda pk.1 pk.2).mp hpk').1
      exact mem_image.mpr ⟨pk.2, mem_Icc.mpr ⟨hk, le_sup hpk⟩, by
        ext <;> simp [heq]⟩
    · intro hpk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hpk
      obtain ⟨hj, hja⟩ := mem_Icc.mp hj
      have hne : s.Nonempty := by
        by_contra h
        have hz : a = 0 := by simp [a, not_nonempty_iff_eq_empty.mp h]
        omega
      obtain ⟨pk, hpk, htop⟩ := exists_mem_eq_sup s hne Prod.snd
      obtain ⟨hpk', heq⟩ := mem_filter.mp hpk
      have hgain := ((mem_full_layers hlambda pk.1 pk.2).mp hpk').2.2
      change pk.1 = p at heq
      change a = pk.2 at htop
      rw [heq, ← htop] at hgain
      apply (hmem j).mpr
      apply (mem_full_layers hlambda p j).mpr
      refine ⟨hj, hp, ?_⟩
      rcases eq_or_lt_of_le hja with rfl | hlt
      · exact hgain
      · exact hgain.trans (golden_layer_strict_decrease hp hj hlt).le
  have hcount : fullCALayerCount lambda p = a := by
    change s.card = a
    rw [hs, card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Nat.card_Icc]
    omega
  rw [← hmem, hs, hcount]
  simp

private theorem largest_ca_pos (lambda : ℝ) : 1 ≤ largestCA lambda := by
  apply Nat.one_le_iff_ne_zero.mpr
  apply prod_ne_zero_iff.mpr
  intro pk hpk
  exact (full_layer_prime lambda hpk).ne_zero

private theorem largest_ca_factorization (lambda : ℝ) (p : ℕ) :
    (largestCA lambda).factorization p = fullCALayerCount lambda p := by
  classical
  unfold largestCA
  rw [Nat.factorization_prod (fun pk hpk => (full_layer_prime lambda hpk).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  calc
    (∑ pk ∈ fullCALayers lambda, pk.1.factorization p) =
        ∑ pk ∈ fullCALayers lambda, if pk.1 = p then 1 else 0 := by
      apply sum_congr rfl
      intro pk hpk
      rw [(full_layer_prime lambda hpk).factorization]
      by_cases h : pk.1 = p <;> simp [h]
    _ = fullCALayerCount lambda p := by simp [fullCALayerCount]

/-- Full-domain positive-price realization: exact inclusive exponents, optimality,
and divisibility of this integer by every positive optimizer. -/
theorem largest_ca_spec {lambda : ℝ} (hlambda : 0 < lambda) :
    1 ≤ largestCA lambda ∧
    (∀ p : ℕ, (largestCA lambda).factorization p = fullCALayerCount lambda p) ∧
    (∀ p : ℕ, ¬p.Prime → fullCALayerCount lambda p = 0) ∧
    (∀ p k : ℕ, p.Prime →
      (1 ≤ k ∧ k ≤ (largestCA lambda).factorization p ↔
        1 ≤ k ∧ lambda ≤ goldenLayerMarginal p k)) ∧
    IsGoldenResourceOptimal lambda (largestCA lambda) ∧
    ∀ m : ℕ, 1 ≤ m → IsGoldenResourceOptimal lambda m → m ∣ largestCA lambda := by
  have hn := largest_ca_pos lambda
  have hc := largest_ca_factorization lambda
  have hi (p k : ℕ) (hp : p.Prime) :
      1 ≤ k ∧ k ≤ (largestCA lambda).factorization p ↔
        1 ≤ k ∧ lambda ≤ goldenLayerMarginal p k := by
    rw [hc, ← full_count_interval hlambda hp k, mem_full_layers hlambda]
    tauto
  refine ⟨hn, hc, fun p hp => nonprime_count lambda hp, hi, ?_, ?_⟩
  · apply (golden_resource_optimal_iff_layer_thresholds hlambda hn).mpr
    constructor
    · intro p hp
      apply le_of_lt
      apply lt_of_not_ge
      intro hgain
      have h := (hi p ((largestCA lambda).factorization p + 1) hp).mpr
        ⟨by omega, hgain⟩
      omega
    · intro p hp hpn
      have hpos := hp.factorization_pos_of_dvd (show largestCA lambda ≠ 0 by omega) hpn
      exact ((hi p ((largestCA lambda).factorization p) hp).mp ⟨hpos, le_rfl⟩).2
  · intro m hm hopt
    apply (Nat.factorization_le_iff_dvd (show m ≠ 0 by omega)
      (show largestCA lambda ≠ 0 by omega)).mp
    intro p
    by_cases hz : m.factorization p = 0
    · simp [hz]
    · have hpos : 1 ≤ m.factorization p := Nat.one_le_iff_ne_zero.mpr hz
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        exact hz)
      have hpn : p ∣ m := Nat.dvd_of_mem_primeFactors (by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        exact hz)
      have hgain := (golden_resource_optimal_iff_layer_thresholds hlambda hm).mp hopt
        |>.2 p hp hpn
      exact ((hi p (m.factorization p) hp).mpr ⟨hpos, hgain⟩).2

private theorem full_layers_subset {lambda1 lambda2 : ℝ} (h2 : 0 < lambda2)
    (h21 : lambda2 < lambda1) : fullCALayers lambda1 ⊆ fullCALayers lambda2 := by
  intro pk hpk
  have h := (mem_full_layers (h2.trans h21) pk.1 pk.2).mp hpk
  exact (mem_full_layers h2 pk.1 pk.2).mpr ⟨h.1, h.2.1, h21.le.trans h.2.2⟩

/-- The consumed actual integer clock. Upper-price ties are already present;
lower-price ties are new. All primes and all layers enter the same finite sum. -/
theorem largest_ca_clock {lambda1 lambda2 : ℝ} (h2 : 0 < lambda2)
    (h21 : lambda2 < lambda1) :
    largestCA lambda1 ∣ largestCA lambda2 ∧
    Real.log (largestCA lambda2 : ℝ) - Real.log (largestCA lambda1 : ℝ) =
      ∑ pk ∈ (fullCALayers lambda2).filter
        (fun pk => goldenLayerMarginal pk.1 pk.2 < lambda1), Real.log (pk.1 : ℝ) := by
  classical
  have hsub := full_layers_subset h2 h21
  have hdiff : fullCALayers lambda2 \ fullCALayers lambda1 =
      (fullCALayers lambda2).filter
        (fun pk => goldenLayerMarginal pk.1 pk.2 < lambda1) := by
    ext pk
    simp only [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨hpk, hnot⟩
      have h := (mem_full_layers h2 pk.1 pk.2).mp hpk
      refine ⟨hpk, lt_of_not_ge fun hge => hnot ?_⟩
      exact (mem_full_layers (h2.trans h21) pk.1 pk.2).mpr ⟨h.1, h.2.1, hge⟩
    · rintro ⟨hpk, hlt⟩
      exact ⟨hpk, fun h => (not_lt_of_ge
        ((mem_full_layers (h2.trans h21) pk.1 pk.2).mp h).2.2) hlt⟩
  have hspec1 := largest_ca_spec (h2.trans h21)
  have hspec2 := largest_ca_spec h2
  have hdiv : largestCA lambda1 ∣ largestCA lambda2 := by
    apply (Nat.factorization_le_iff_dvd (show largestCA lambda1 ≠ 0 by omega)
      (show largestCA lambda2 ≠ 0 by omega)).mp
    intro p
    rw [hspec1.2.1 p, hspec2.2.1 p]
    exact card_le_card (filter_subset_filter _ hsub)
  refine ⟨hdiv, ?_⟩
  have hlog (lambda : ℝ) : Real.log (largestCA lambda : ℝ) =
      ∑ pk ∈ fullCALayers lambda, Real.log (pk.1 : ℝ) := by
    unfold largestCA
    rw [Nat.cast_prod, Real.log_prod]
    intro pk hpk
    exact_mod_cast (full_layer_prime lambda hpk).ne_zero
  rw [hlog, hlog, ← hdiff]
  have hsum := sum_sdiff (f := fun pk : ℕ × ℕ => Real.log (pk.1 : ℝ)) hsub
  linarith

#print axioms largest_ca_spec
#print axioms largest_ca_clock

end
end D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer
