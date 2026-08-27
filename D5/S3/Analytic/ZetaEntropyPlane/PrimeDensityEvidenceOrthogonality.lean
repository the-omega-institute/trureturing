/- GID: D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime counts vanish in N while reciprocal evidence diverges; empty support converges. -/
/- Library-search audit trail (2026-08-25): repository search found the exponent
   threshold module `PrimeEvidenceSharpThreshold`, whose exponent-one divergence
   and exponent-two convergence theorems are reused directly. Pinned mathlib has
   no natural-density API: `MeasureTheory.Function.Intersectivity` explicitly
   records that API as a TODO. `Chebyshev.eventually_primeCounting_le` supplies
   the prime-counting bound used for the documented density downgrade. -/

import Mathlib.NumberTheory.Chebyshev
import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality

open Filter Finset Asymptotics
open scoped Topology Nat.Prime
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

noncomputable section

/-!
This module concerns the size of the index set, unlike 235.2, which proves the
exponent threshold `Summable (primeEvidence s) ↔ 1 < s` for a fixed index set.

Pinned mathlib lacks a natural-density API, so "sparse" is downgraded here to
vanishing counting ratio in `ℕ`. Thus the divergent set is all primes viewed as
a subset of `ℕ`; it has density zero there, but density one relative to the prime
subtype. This is weaker than the source phrase "relative density zero among
primes". Primality is load-bearing twice: Chebyshev gives the counting estimate,
and Euler's theorem gives divergence of the reciprocal-prime series.
-/

/-- The proportion of members of `S` in the integer interval from one through `n`. -/
noncomputable def naturalCountingRatio (S : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact (((Finset.Icc 1 n).filter fun k => k ∈ S).card : ℝ) / (n : ℝ)

/-- The set of prime natural numbers, used as the sparse subset of `ℕ`. -/
def primeNaturals : Set ℕ :=
  {p | p.Prime}

/-- Prime evidence restricted to those prime values whose naturals lie in `S`. -/
noncomputable def restrictedPrimeEvidence (S : Set ℕ) (s : ℝ)
    (p : Nat.Primes) : ℝ := by
  classical
  exact if p.1 ∈ S then primeEvidence s p else 0

/-- At `n = 0`, every counting ratio is zero under Lean's totalized division. -/
theorem naturalCountingRatio_zero (S : Set ℕ) :
    naturalCountingRatio S 0 = 0 := by
  simp [naturalCountingRatio]

#print axioms naturalCountingRatio_zero

/-- The counting ratio for prime naturals is the usual prime-counting ratio. -/
theorem primeNaturals_countingRatio (n : ℕ) :
    naturalCountingRatio primeNaturals n =
      (Nat.primeCounting n : ℝ) / (n : ℝ) := by
  classical
  simp only [naturalCountingRatio, primeNaturals, Set.mem_setOf_eq]
  change (((Finset.Icc 1 n).filter Nat.Prime).card : ℝ) / (n : ℝ) = _
  rw [← Nat.primesLE_eq_filter_Icc_one]
  simp

#print axioms primeNaturals_countingRatio

/-- All primes are sparse in `ℕ`, yet their reciprocal evidence is nonsummable. -/
theorem sparse_prime_support_diverges :
    Tendsto (naturalCountingRatio primeNaturals) atTop (nhds 0) ∧
      ¬ Summable (restrictedPrimeEvidence primeNaturals 1) := by
  have hbig :
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) =O[atTop]
        (fun x : ℝ => x / Real.log x) := by
    refine IsBigO.of_bound (Real.log 4 + 1) ?_
    filter_upwards [Chebyshev.eventually_primeCounting_le
      (by norm_num : (0 : ℝ) < 1), eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hnum : 0 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
    have hden : 0 ≤ x / Real.log x :=
      div_nonneg (le_trans (by norm_num) hx1.le) hlog
    rw [mul_div_assoc] at hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnum, abs_of_nonneg hden] using hx
  have hsmall :
      (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx hzero
      exact (hx hzero).elim
    · have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
        Real.tendsto_log_atTop.inv_tendsto_atTop
      apply hinv.congr'
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp
  have hreal :
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) =o[atTop] (fun x : ℝ => x) :=
    hbig.trans_isLittleO hsmall
  have hnat :
      (fun n : ℕ => (Nat.primeCounting n : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ)) := by
    simpa using hreal.natCast_atTop
  constructor
  · convert hnat.tendsto_div_nhds_zero using 1
    ext n
    exact primeNaturals_countingRatio n
  · have heq :
        restrictedPrimeEvidence primeNaturals 1 = primeEvidence 1 := by
      funext p
      simp only [restrictedPrimeEvidence, primeNaturals, Set.mem_setOf_eq,
        p.2, if_true]
    rw [heq]
    exact primeEvidence_one_not_summable

#print axioms sparse_prime_support_diverges

/-- Relative to the prime subtype the same support is full, while square evidence is summable. -/
theorem full_prime_support_square_evidence_summable :
    (∀ p : Nat.Primes, p.1 ∈ primeNaturals) ∧
      Summable (restrictedPrimeEvidence primeNaturals 2) := by
  constructor
  · exact fun p => p.2
  · have heq :
        restrictedPrimeEvidence primeNaturals 2 = primeEvidence 2 := by
      funext p
      simp only [restrictedPrimeEvidence, primeNaturals, Set.mem_setOf_eq,
        p.2, if_true]
    rw [heq]
    exact primeEvidence_two_summable

#print axioms full_prime_support_square_evidence_summable

/-- Empty support has the same zero counting limit as primes, but all its evidence sums. -/
theorem empty_support_sparse_and_summable :
    Tendsto (naturalCountingRatio ∅) atTop (nhds 0) ∧
      Summable (restrictedPrimeEvidence ∅ 1) := by
  classical
  constructor
  · have hzero : naturalCountingRatio ∅ = fun _ : ℕ => 0 := by
      funext n
      simp [naturalCountingRatio]
    rw [hzero]
    exact tendsto_const_nhds
  · have hzero :
        restrictedPrimeEvidence ∅ 1 = fun _ : Nat.Primes => 0 := by
      funext p
      simp [restrictedPrimeEvidence]
    rw [hzero]
    exact summable_zero

#print axioms empty_support_sparse_and_summable

/-- Every singleton prime support is summable, independently of the exponent. -/
theorem singleton_prime_support_summable (q : Nat.Primes) (s : ℝ) :
    Summable (restrictedPrimeEvidence {q.1} s) := by
  refine (hasSum_single q ?_).summable
  intro p hp
  have hval : p.1 ≠ q.1 := fun h => hp (Subtype.ext h)
  simp [restrictedPrimeEvidence, hval]

#print axioms singleton_prime_support_summable

/-- Zero counting density admits both convergence and divergence, while full prime support
can also carry convergent evidence; index-set size alone is therefore insufficient. -/
theorem counting_density_not_sufficient_for_summability :
    (Tendsto (naturalCountingRatio primeNaturals) atTop (nhds 0) ∧
      ¬ Summable (restrictedPrimeEvidence primeNaturals 1)) ∧
    ((∀ p : Nat.Primes, p.1 ∈ primeNaturals) ∧
      Summable (restrictedPrimeEvidence primeNaturals 2)) ∧
    (Tendsto (naturalCountingRatio ∅) atTop (nhds 0) ∧
      Summable (restrictedPrimeEvidence ∅ 1)) := by
  exact ⟨sparse_prime_support_diverges,
    full_prime_support_square_evidence_summable,
    empty_support_sparse_and_summable⟩

#print axioms counting_density_not_sufficient_for_summability

end


end D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality
