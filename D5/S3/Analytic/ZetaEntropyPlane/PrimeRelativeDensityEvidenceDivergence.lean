/- GID: D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: 0/1/finite witnesses; square support has zero density and divergent evidence. -/
/- Library-search audit trail (2026-08-25): repository searches for relative prime
   density, sparse prime support, reciprocal mass, and prime-index variants found only
   `PrimeDensityEvidenceOrthogonality`, whose module comment records this exact gap.
   Local smart searches for nth-prime and prime-counting asymptotics had no direct hit.
   Pinned Mathlib supplies `Nat.primeCounting'_nth_eq`, `Nat.nth_count`, `Nat.sqrt_eq'`,
   `Finset.card_le_card_of_injOn`, `Summable.comp_injective`, and the harmonic-series
   divergence theorem. No declaration packages the zero-relative-density example. -/

import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Sqrt
import D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PrimeRelativeDensityEvidenceDivergence

open Filter Finset
open scoped Topology Nat.Prime
open D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality

noncomputable section

/-- The increasing prime enumeration, packaged with its inverse prime index. -/
noncomputable def primeIndexEquiv : ℕ ≃ Nat.Primes where
  toFun n := ⟨Nat.nth Nat.Prime n, Nat.prime_nth_prime n⟩
  invFun p := Nat.primeCounting' p.1
  left_inv n := Nat.primeCounting'_nth_eq n
  right_inv p := by
    apply Subtype.ext
    exact Nat.nth_count p.2

/-- The proportion of the first `n` primes that lie in `S`. -/
noncomputable def relativePrimeCountingRatio (S : Set Nat.Primes) (n : ℕ) : ℝ := by
  classical
  exact (((Finset.range n).filter fun k => primeIndexEquiv k ∈ S).card : ℝ) / (n : ℝ)

/-- The primes whose zero-based indices are perfect squares. -/
def squareIndexedPrimeSupport : Set Nat.Primes :=
  Set.range fun k => primeIndexEquiv (k ^ 2)

/-- Harmonic evidence on square-indexed primes, and zero evidence elsewhere. -/
noncomputable def squareIndexedPrimeEvidence (p : Nat.Primes) : ℝ :=
  by
    classical
    exact if p ∈ squareIndexedPrimeSupport then
      1 / ((Nat.sqrt (primeIndexEquiv.symm p) : ℝ) + 1)
    else 0

/-- At the zero cutoff every relative prime counting ratio is exactly zero. -/
theorem relativePrimeCountingRatio_zero (S : Set Nat.Primes) :
    relativePrimeCountingRatio S 0 = 0 := by
  simp [relativePrimeCountingRatio]

#print axioms relativePrimeCountingRatio_zero

/-- Empty prime support has relative density exactly zero. -/
theorem empty_relative_prime_density_zero :
    Tendsto (relativePrimeCountingRatio ∅) atTop (nhds 0) := by
  have hzero : relativePrimeCountingRatio ∅ = fun _ : ℕ => 0 := by
    funext n
    simp [relativePrimeCountingRatio]
  rw [hzero]
  exact tendsto_const_nhds

#print axioms empty_relative_prime_density_zero

/-- Full prime support has relative density exactly one. -/
theorem full_relative_prime_density_one :
    Tendsto (relativePrimeCountingRatio Set.univ) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  simp [relativePrimeCountingRatio, hn]

#print axioms full_relative_prime_density_one

private theorem singleton_relative_prime_density_zero (q : Nat.Primes) :
    Tendsto (relativePrimeCountingRatio {q}) atTop (nhds 0) := by
  classical
  have hmodel : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    have hfun : (Nat.cast : ℕ → ℝ)⁻¹ = fun n : ℕ => (1 : ℝ) / (n : ℝ) := by
      funext n
      simp [Pi.inv_apply, one_div]
    rw [hfun] at h
    exact h
  refine squeeze_zero' ?_ ?_ hmodel
  · exact Eventually.of_forall fun n => by
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun n => by
      rw [relativePrimeCountingRatio]
      rw [Finset.filter_congr_decidable]
      apply div_le_div_of_nonneg_right ?_
        (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg _)
      norm_cast
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      exact primeIndexEquiv.injective (ha'.2.trans hb'.2.symm)

/-- A singleton has relative density zero and finite evidence support for every exponent. -/
theorem singleton_relative_prime_density_zero_and_summable
    (q : Nat.Primes) (s : ℝ) :
    Tendsto (relativePrimeCountingRatio {q}) atTop (nhds 0) ∧
      Summable (restrictedPrimeEvidence {q.1} s) := by
  exact ⟨singleton_relative_prime_density_zero q,
    singleton_prime_support_summable q s⟩

#print axioms singleton_relative_prime_density_zero_and_summable

private theorem indexedPrime_mem_square_support_iff (n : ℕ) :
    primeIndexEquiv n ∈ squareIndexedPrimeSupport ↔ ∃ k, k ^ 2 = n := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, primeIndexEquiv.injective hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

open scoped Classical in
private theorem square_index_card_le (n : ℕ) :
    ((Finset.range n).filter fun k => primeIndexEquiv k ∈ squareIndexedPrimeSupport).card ≤
      Nat.sqrt n + 1 := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (s := (Finset.range n).filter fun k => primeIndexEquiv k ∈ squareIndexedPrimeSupport)
    (t := Finset.range (Nat.sqrt n + 1)) Nat.sqrt
    (by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hklt : k < n := Finset.mem_range.mp hk'.1
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_sqrt hklt.le)))
    (by
      intro a ha b hb hsqrt
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      obtain ⟨ka, hka⟩ := (indexedPrime_mem_square_support_iff a).mp ha'.2
      obtain ⟨kb, hkb⟩ := (indexedPrime_mem_square_support_iff b).mp hb'.2
      calc
        a = Nat.sqrt a ^ 2 := by rw [← hka, Nat.sqrt_eq']
        _ = Nat.sqrt b ^ 2 := by rw [hsqrt]
        _ = b := by rw [← hkb, Nat.sqrt_eq'])
  simpa using hcard

/-- Square-indexed primes have relative density zero among all primes. -/
theorem square_indexed_prime_support_relative_density_zero :
    Tendsto (relativePrimeCountingRatio squareIndexedPrimeSupport) atTop (nhds 0) := by
  have hsqrtNat : Tendsto (fun n : ℕ => Nat.sqrt n) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b ^ 2, ?_⟩
    intro n hn
    exact Nat.le_sqrt'.mpr hn
  have hsqrtReal : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsqrtNat
  have hmodel : Tendsto
      (fun n : ℕ => (1 : ℝ) / Nat.sqrt n + 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [Pi.inv_apply, one_div, add_zero] using
      hsqrtReal.inv_tendsto_atTop.add tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hsqrtPos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
    have hsquare : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ (n : ℝ) := by
      exact_mod_cast Nat.sqrt_le n
    have hfrac : (Nat.sqrt n : ℝ) / n ≤ 1 / Nat.sqrt n := by
      rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hsqrtPos)]
      simpa using hsquare
    calc
      relativePrimeCountingRatio squareIndexedPrimeSupport n ≤
          ((Nat.sqrt n + 1 : ℕ) : ℝ) / n := by
        rw [relativePrimeCountingRatio]
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast square_index_card_le n) (Nat.cast_nonneg _)
      _ = (Nat.sqrt n : ℝ) / n + 1 / n := by norm_num [add_div]
      _ ≤ 1 / Nat.sqrt n + 1 / n := add_le_add_left hfrac _
  · exact hmodel

#print axioms square_indexed_prime_support_relative_density_zero

private theorem squareIndexedPrimeEvidence_apply (k : ℕ) :
    squareIndexedPrimeEvidence (primeIndexEquiv (k ^ 2)) = 1 / ((k : ℝ) + 1) := by
  rw [squareIndexedPrimeEvidence, if_pos ⟨k, rfl⟩]
  simp [Nat.sqrt_eq']

/-- Harmonic evidence on square-indexed primes is not summable. -/
theorem square_indexed_prime_evidence_not_summable :
    ¬ Summable squareIndexedPrimeEvidence := by
  intro hsummable
  have hinjective : Function.Injective (fun k : ℕ => primeIndexEquiv (k ^ 2)) :=
    primeIndexEquiv.injective.comp (Nat.pow_left_injective (by norm_num : 2 ≠ 0))
  have hsubseries := hsummable.comp_injective hinjective
  have hharmonic : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) :=
    hsubseries.congr fun k => squareIndexedPrimeEvidence_apply k
  have hnot : ¬ Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      mt (_root_.summable_nat_add_iff 1).mp Real.not_summable_one_div_natCast
  exact hnot hharmonic

#print axioms square_indexed_prime_evidence_not_summable

/-- A named zero-relative-density prime support still carries divergent evidence. -/
theorem zero_relative_prime_density_with_divergent_evidence :
    Tendsto (relativePrimeCountingRatio squareIndexedPrimeSupport) atTop (nhds 0) ∧
      ¬ Summable squareIndexedPrimeEvidence := by
  exact ⟨square_indexed_prime_support_relative_density_zero,
    square_indexed_prime_evidence_not_summable⟩

#print axioms zero_relative_prime_density_with_divergent_evidence

/-- FPOD Corollary 216.1: counting spectra and cumulative evidence are independent. -/
theorem prime_relative_density_does_not_determine_evidence_summability :
    ((Tendsto (naturalCountingRatio primeNaturals) atTop (nhds 0) ∧
      ¬ Summable (restrictedPrimeEvidence primeNaturals 1)) ∧
      ((∀ p : Nat.Primes, p.1 ∈ primeNaturals) ∧
        Summable (restrictedPrimeEvidence primeNaturals 2)) ∧
      (Tendsto (naturalCountingRatio ∅) atTop (nhds 0) ∧
        Summable (restrictedPrimeEvidence ∅ 1))) ∧
    (Tendsto (relativePrimeCountingRatio squareIndexedPrimeSupport) atTop (nhds 0) ∧
      ¬ Summable squareIndexedPrimeEvidence) ∧
    (Tendsto (relativePrimeCountingRatio Set.univ) atTop (nhds 1) ∧
      Summable (restrictedPrimeEvidence primeNaturals 2)) := by
  exact ⟨counting_density_not_sufficient_for_summability,
    zero_relative_prime_density_with_divergent_evidence,
    full_relative_prime_density_one,
    full_prime_support_square_evidence_summable.2⟩

#print axioms prime_relative_density_does_not_determine_evidence_summability

end

end D5.S3.Analytic.ZetaEntropyPlane.PrimeRelativeDensityEvidenceDivergence
