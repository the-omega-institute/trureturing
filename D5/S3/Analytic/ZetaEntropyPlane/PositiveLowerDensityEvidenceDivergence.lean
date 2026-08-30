/- GID: D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive lower prime density forces reciprocal evidence divergence; zero cases do not. -/
/- Library-search audit trail (2026-08-25): repository searches by theorem name,
   digest, lower-density terminology, general summability shape, and Kakutani
   vocabulary found only the full-prime special case reused below. Pinned mathlib
   has no natural-density API and no product-measure Kakutani dichotomy. Exact
   hits `Nat.nth_lt_of_lt_count`, `summable_indicator_mod_iff`,
   `Equiv.summable_iff`, and `Summable.of_norm_bounded_eventually` support comparison. -/

import Mathlib.Analysis.SumOverResidueClass
import D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PositiveLowerDensityEvidenceDivergence

open Filter
open scoped Topology Nat.Prime
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality

noncomputable section

/-- The fraction of the first `n` primes whose natural values lie in `S`. -/
noncomputable def primeRelativeCountingRatio (S : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact (Nat.count (fun k => Nat.nth Nat.Prime k ∈ S) n : ℝ) / (n : ℝ)

/-- A set of primes has positive lower relative density when its prime-index
count is eventually bounded below by a fixed positive reciprocal integer. -/
noncomputable def HasPositiveLowerRelativeDensity (S : Set ℕ) : Prop := by
  classical
  exact ∃ m : ℕ, 0 < m ∧
    ∀ᶠ n in atTop,
      n ≤ m * Nat.count (fun k => Nat.nth Nat.Prime k ∈ S) n

/-- At `n = 0`, every prime-relative counting ratio is zero. -/
theorem primeRelativeCountingRatio_zero (S : Set ℕ) :
    primeRelativeCountingRatio S 0 = 0 := by
  simp [primeRelativeCountingRatio]

#print axioms primeRelativeCountingRatio_zero

/-- Empty prime support has relative counting ratio identically zero. -/
theorem empty_primeRelativeCountingRatio_tendsto_zero :
    Tendsto (primeRelativeCountingRatio ∅) atTop (nhds 0) := by
  have hzero : primeRelativeCountingRatio ∅ = fun _ : ℕ => 0 := by
    funext n
    simp [primeRelativeCountingRatio]
  rw [hzero]
  exact tendsto_const_nhds

#print axioms empty_primeRelativeCountingRatio_tendsto_zero

/-- The empty set has lower relative density zero, not positive lower density. -/
theorem empty_not_hasPositiveLowerRelativeDensity :
    ¬ HasPositiveLowerRelativeDensity ∅ := by
  rintro ⟨m, hm, hbound⟩
  have hlarge := (hbound.and (eventually_gt_atTop (m * 0))).exists
  rcases hlarge with ⟨n, hn, hgt⟩
  simp only [Set.mem_empty_iff_false, Nat.count_false, mul_zero] at hn
  exact (not_lt_of_ge hn) hgt

#print axioms empty_not_hasPositiveLowerRelativeDensity

/-- The full prime support has positive lower relative density. -/
theorem primeNaturals_hasPositiveLowerRelativeDensity :
    HasPositiveLowerRelativeDensity primeNaturals := by
  refine ⟨1, by omega, ?_⟩
  filter_upwards [] with n
  simp [primeNaturals]

#print axioms primeNaturals_hasPositiveLowerRelativeDensity

/-- Reciprocal prime evidence diverges on every positive-lower-density prime support. -/
theorem restricted_reciprocal_evidence_not_summable
    (S : Set ℕ) (hS : HasPositiveLowerRelativeDensity S) :
    ¬ Summable (restrictedPrimeEvidence S 1) := by
  classical
  let A : ℕ → Prop := fun k => Nat.nth Nat.Prime k ∈ S
  obtain ⟨m, hm, hbound⟩ := hS
  change ∀ᶠ n in atTop, n ≤ m * Nat.count A n at hbound
  have hA : {k : ℕ | A k}.Infinite := by
    intro hfinite
    obtain ⟨n, hn, hlarge⟩ :=
      (hbound.and (eventually_gt_atTop (m * hfinite.toFinset.card))).exists
    have hcount : Nat.count A n ≤ hfinite.toFinset.card :=
      Nat.count_le_card hfinite n
    exact (not_lt_of_ge (hn.trans (Nat.mul_le_mul_left m hcount))) hlarge
  let primeAt : ℕ → Nat.Primes := fun k =>
    ⟨Nat.nth Nat.Prime k, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k⟩
  let selectedPrime : ℕ → Nat.Primes := fun k => primeAt (Nat.nth A k)
  have hselected_injective : Function.Injective selectedPrime := by
    intro a b hab
    apply (Nat.nth_injective hA)
    apply Nat.nth_injective Nat.infinite_setOf_prime
    exact congrArg Subtype.val hab
  intro hsum
  have hselected_restricted :
      Summable (fun k => restrictedPrimeEvidence S 1 (selectedPrime k)) :=
    hsum.comp_injective hselected_injective
  have hselected : Summable (fun k => primeEvidence 1 (selectedPrime k)) := by
    apply hselected_restricted.congr
    intro k
    have hk : A (Nat.nth A k) := Nat.nth_mem_of_infinite hA k
    simp only [restrictedPrimeEvidence, selectedPrime, primeAt]
    rw [if_pos hk]
  let primeOrder : ℕ ≃ Nat.Primes :=
    (@Nat.Subtype.orderIsoOfNat {p : ℕ | Nat.Prime p}
      Nat.infinite_setOf_prime.to_subtype).toEquiv
  have hprimeAt : primeAt = primeOrder := by
    funext k
    apply Subtype.ext
    exact Nat.nth_apply_eq_orderIsoOfNat Nat.infinite_setOf_prime k
  let f : ℕ → ℝ := fun k => primeEvidence 1 (primeAt k)
  have hf_not_summable : ¬ Summable f := by
    rw [show f = primeEvidence 1 ∘ primeOrder by
      funext k
      simp only [f, Function.comp_apply, hprimeAt]]
    rw [primeOrder.summable_iff]
    intro hprime
    apply sparse_prime_support_diverges.2
    apply hprime.congr
    intro p
    simp [restrictedPrimeEvidence, primeNaturals]
  have hf_antitone : Antitone f := by
    intro a b hab
    simp only [f, primeEvidence, Real.rpow_neg_one]
    have hpos : (0 : ℝ) < (primeAt a).1 := by
      exact_mod_cast (primeAt a).2.pos
    have hle : ((primeAt a).1 : ℝ) ≤ (primeAt b).1 := by
      exact_mod_cast Nat.nth_monotone Nat.infinite_setOf_prime hab
    simpa only [one_div] using one_div_le_one_div_of_le hpos hle
  letI : NeZero m := ⟨hm.ne'⟩
  have hstep_not_summable : ¬ Summable (fun k => f (m * k + m)) := by
    rw [← summable_indicator_mod_iff_summable m m f]
    rw [summable_indicator_mod_iff hf_antitone (m : ZMod m)]
    exact hf_not_summable
  have hscale : Tendsto (fun k : ℕ => m * (k + 1)) atTop atTop := by
    refine tendsto_atTop.2 fun n => ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    calc
      n ≤ k := hk
      _ ≤ 1 * (k + 1) := by simp
      _ ≤ m * (k + 1) := Nat.mul_le_mul_right (k + 1) hm
  have hindex_bound :
      ∀ᶠ k in atTop, Nat.nth A k < m * (k + 1) := by
    filter_upwards [hscale.eventually hbound] with k hk
    apply Nat.nth_lt_of_lt_count
    exact Nat.lt_of_succ_le (le_of_mul_le_mul_left hk hm)
  apply hstep_not_summable
  apply hselected.of_norm_bounded_eventually_nat
  filter_upwards [hindex_bound] with k hk
  have hcompare : f (m * k + m) ≤ primeEvidence 1 (selectedPrime k) := by
    change f (m * k + m) ≤ f (Nat.nth A k)
    apply hf_antitone
    simpa only [Nat.mul_add, Nat.mul_one] using hk.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (primeEvidence_pos 1 _)),
    f, selectedPrime] using hcompare

#print axioms restricted_reciprocal_evidence_not_summable

/-- An eventual `c / p` lower bound on a positive-lower-density support makes
the entire real evidence family nonsummable. -/
theorem positive_lower_density_evidence_not_summable
    (S : Set ℕ) (hS : HasPositiveLowerRelativeDensity S)
    (e : Nat.Primes → ℝ) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ᶠ p in cofinite,
      p.1 ∈ S → c * primeEvidence 1 p ≤ e p) :
    ¬ Summable e := by
  intro he
  apply restricted_reciprocal_evidence_not_summable S hS
  have hmajor : Summable (fun p => c⁻¹ * ‖e p‖) :=
    he.norm.mul_left c⁻¹
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [hbound] with p hp
  by_cases hpS : p.1 ∈ S
  · simp only [restrictedPrimeEvidence, hpS, if_true, Real.norm_eq_abs,
      abs_of_pos (primeEvidence_pos 1 p)]
    rw [le_inv_mul_iff₀ hc]
    exact (hp hpS).trans (le_abs_self (e p))
  · simp [restrictedPrimeEvidence, hpS, mul_nonneg (inv_nonneg.mpr hc.le)]

#print axioms positive_lower_density_evidence_not_summable

/-- Constant-zero evidence is summable on the prime subtype. -/
theorem zero_prime_evidence_summable :
    Summable (fun _ : Nat.Primes => (0 : ℝ)) := by
  exact summable_zero

#print axioms zero_prime_evidence_summable

/-- Positivity of the comparison coefficient is necessary: coefficient zero
allows constant-zero evidence even on full prime support. -/
theorem positive_coefficient_is_necessary :
    HasPositiveLowerRelativeDensity primeNaturals ∧
      (∀ᶠ p : Nat.Primes in cofinite,
        p.1 ∈ primeNaturals →
          (0 : ℝ) * primeEvidence 1 p ≤ 0) ∧
      Summable (fun _ : Nat.Primes => (0 : ℝ)) := by
  refine ⟨primeNaturals_hasPositiveLowerRelativeDensity, ?_,
    zero_prime_evidence_summable⟩
  filter_upwards [] with p
  simp

#print axioms positive_coefficient_is_necessary

/-- Positive lower density is necessary: the empty support makes the lower
bound vacuous while constant-zero evidence remains summable. -/
theorem positive_lower_density_is_necessary :
    ¬ HasPositiveLowerRelativeDensity ∅ ∧
      (∀ᶠ p : Nat.Primes in cofinite,
        p.1 ∈ (∅ : Set ℕ) →
          (1 : ℝ) * primeEvidence 1 p ≤ 0) ∧
      Summable (fun _ : Nat.Primes => (0 : ℝ)) := by
  refine ⟨empty_not_hasPositiveLowerRelativeDensity, ?_,
    zero_prime_evidence_summable⟩
  filter_upwards [] with p
  simp

#print axioms positive_lower_density_is_necessary

/-- The reciprocal lower bound is necessary: constant-zero evidence on full
prime support is summable but violates every coefficient-one bound. -/
theorem reciprocal_lower_bound_is_necessary :
    HasPositiveLowerRelativeDensity primeNaturals ∧
      ¬ (∀ᶠ p : Nat.Primes in cofinite,
        p.1 ∈ primeNaturals →
          (1 : ℝ) * primeEvidence 1 p ≤ 0) ∧
      Summable (fun _ : Nat.Primes => (0 : ℝ)) := by
  refine ⟨primeNaturals_hasPositiveLowerRelativeDensity, ?_,
    zero_prime_evidence_summable⟩
  intro hbound
  have hfalse : ∀ᶠ p : Nat.Primes in cofinite, False := by
    filter_upwards [hbound] with p hp
    have hpfull : p.1 ∈ primeNaturals := p.2
    exact (not_le_of_gt (primeEvidence_pos 1 p)) (by simpa using hp hpfull)
  rcases hfalse.exists with ⟨p, hp⟩
  exact hp.elim

#print axioms reciprocal_lower_bound_is_necessary

end

end D5.S3.Analytic.ZetaEntropyPlane.PositiveLowerDensityEvidenceDivergence
