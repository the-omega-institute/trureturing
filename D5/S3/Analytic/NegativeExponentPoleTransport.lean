/- GID: D5/S3/Analytic/NegativeExponentPoleTransport
   generality: G
   mirror-B: D5/B/S3/Analytic/NegativeExponentPoleTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Negative exponents transport positive-order zeros into exact pole debts. -/

/- Library-search audit (2026-09-04):
   * Pinned Mathlib's `meromorphicOrderAt_prod` and
     `meromorphicOrderAt_zpow` give the finite-dictionary order identity.
   * `tendsto_cobounded_iff_meromorphicOrderAt_neg` identifies negative
     order with a genuine punctured-neighborhood pole.
   * Repository searches found local special-purpose order calculations but
     no finite dictionary theorem with a distinguished negative exponent and
     an exact cancellation criterion. The source atom's RH and numerical
     window claims have no supplied formal certificates and are not asserted. -/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.NegativeExponentPoleTransport

open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/-- A finite meromorphic dictionary with an integer exponent on every factor. -/
def dictionaryProduct {ι : Type*} [DecidableEq ι]
    (support : Finset ι) (factor : ι → ℂ → ℂ) (exponent : ι → ℤ) : ℂ → ℂ :=
  ∏ i ∈ support, (factor i) ^ exponent i

/-- The local order of a finite dictionary is the distinguished contribution
plus the sum of all remaining possible cancellation channels. -/
theorem dictionary_order_split {ι : Type*} [DecidableEq ι]
    (support : Finset ι) (factor : ι → ℂ → ℂ) (exponent : ι → ℤ)
    (point : ℂ) (distinguished : ι) (hDistinguished : distinguished ∈ support)
    (hMeromorphic : ∀ i ∈ support, MeromorphicAt (factor i) point) :
    meromorphicOrderAt (dictionaryProduct support factor exponent) point =
      exponent distinguished * meromorphicOrderAt (factor distinguished) point +
        ∑ i ∈ support.erase distinguished,
          exponent i * meromorphicOrderAt (factor i) point := by
  calc
    meromorphicOrderAt (dictionaryProduct support factor exponent) point =
        meromorphicOrderAt (∏ i ∈ support, (factor i) ^ exponent i) point := rfl
    _ = ∑ i ∈ support, meromorphicOrderAt ((factor i) ^ exponent i) point :=
      meromorphicOrderAt_prod fun i hi => (hMeromorphic i hi).zpow (exponent i)
    _ = ∑ i ∈ support,
        exponent i * meromorphicOrderAt (factor i) point := by
      apply Finset.sum_congr rfl
      intro i hi
      exact meromorphicOrderAt_zpow (hMeromorphic i hi)
    _ = exponent distinguished * meromorphicOrderAt (factor distinguished) point +
        ∑ i ∈ support.erase distinguished,
          exponent i * meromorphicOrderAt (factor i) point :=
      (support.add_sum_erase
      (fun i => exponent i * meromorphicOrderAt (factor i) point)
      hDistinguished).symm

/-- A negative exponent turns a positive-order zero into a negative order
contribution. The product has a pole exactly when the other factors fail to
cancel that debt; absence of a pole is exactly nonnegativity of the total
order. -/
theorem negative_exponent_pole_transport {ι : Type*} [DecidableEq ι]
    (support : Finset ι) (factor : ι → ℂ → ℂ) (exponent : ι → ℤ)
    (point : ℂ) (distinguished : ι) (multiplicity : ℤ)
    (hDistinguished : distinguished ∈ support)
    (hExponent : exponent distinguished < 0) (hMultiplicity : 0 < multiplicity)
    (hMeromorphic : ∀ i ∈ support, MeromorphicAt (factor i) point)
    (hDistinguishedOrder :
      meromorphicOrderAt (factor distinguished) point = multiplicity) :
    meromorphicOrderAt (dictionaryProduct support factor exponent) point =
        exponent distinguished * meromorphicOrderAt (factor distinguished) point +
          ∑ i ∈ support.erase distinguished,
            exponent i * meromorphicOrderAt (factor i) point ∧
      exponent distinguished * meromorphicOrderAt (factor distinguished) point < 0 ∧
      (Tendsto (dictionaryProduct support factor exponent) (𝓝[≠] point)
          (Bornology.cobounded ℂ) ↔
        exponent distinguished * meromorphicOrderAt (factor distinguished) point +
            ∑ i ∈ support.erase distinguished,
              exponent i * meromorphicOrderAt (factor i) point < 0) ∧
      (¬Tendsto (dictionaryProduct support factor exponent) (𝓝[≠] point)
          (Bornology.cobounded ℂ) ↔
        0 ≤ exponent distinguished * meromorphicOrderAt (factor distinguished) point +
            ∑ i ∈ support.erase distinguished,
              exponent i * meromorphicOrderAt (factor i) point) := by
  have hSplit := dictionary_order_split support factor exponent point distinguished
    hDistinguished hMeromorphic
  have hDebt :
      exponent distinguished * meromorphicOrderAt (factor distinguished) point < 0 := by
    rw [hDistinguishedOrder]
    norm_cast
    exact mul_neg_of_neg_of_pos hExponent hMultiplicity
  have hProductMeromorphic :
      MeromorphicAt (dictionaryProduct support factor exponent) point := by
    unfold dictionaryProduct
    exact MeromorphicAt.prod fun i hi => (hMeromorphic i hi).zpow (exponent i)
  have hPole := tendsto_cobounded_iff_meromorphicOrderAt_neg hProductMeromorphic
  rw [hSplit] at hPole
  refine ⟨hSplit, hDebt, hPole, ?_⟩
  rw [hPole, not_lt]

end

end D5.S3.Analytic.NegativeExponentPoleTransport
