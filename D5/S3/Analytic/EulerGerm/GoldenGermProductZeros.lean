/- GID: D5/S3/Analytic/EulerGerm/GoldenGermProductZeros
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermProductZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For Re s > 1/phi^2, zeros localize at 2 and are isolated; existence stays open. -/

import D5.S3.Analytic.EulerGerm.GermProductAnalytic
import D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds

/- Search audit (2026-08-28):
   * Reused the frozen product analyticity theorem, the odd-prime local
     nonvanishing theorem on `1 / phi^2 < Re s`, and product nonvanishing on
     `2 / 3 <= Re s`. The strict inequality points to the right, while the
     latter weak inequality includes its boundary.
   * Pinned Mathlib supplies `tprod_of_exists_eq_zero`,
     `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, the analytic
     identity theorem on preconnected sets, and convexity of linear
     half-spaces. No one of these already states this Euler-germ result.
   * The theorem does not decide whether a zero exists in
     `1 / phi^2 < Re s < 2 / 3`; it proves only localization and isolation. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermProductZeros

open D5.S3.Analytic.EulerGerm.GermProductAnalytic
open D5.S3.Analytic.EulerGerm.GermProductNonvanishing
open D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open scoped Topology

noncomputable section

/-- On the open half-plane `1 / phi^2 < Re s`, the golden Euler product is
nonzero exactly when its prime-2 local factor is nonzero. The point `s = 1`
lies in this half-plane and has nonzero product, so the analytic product is not
identically zero there. Every point of the half-plane has a punctured
neighborhood free of product zeros and prime-2 local-factor zeros. This does
not assert that any zero exists below `Re s = 2 / 3`. -/
theorem golden_germ_product_zeros :
    1 / Real.goldenRatio ^ 2 < (1 : ℂ).re ∧
      (∏' p : Nat.Primes, germLocalFactor (1 : ℂ) p) ≠ 0 ∧
      (∀ s : ℂ, 1 / Real.goldenRatio ^ 2 < s.re →
        ((∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 ↔
          germLocalFactor s 2 ≠ 0)) ∧
      (∀ z : ℂ, 1 / Real.goldenRatio ^ 2 < z.re →
        ∀ᶠ w in 𝓝[≠] z, (∏' p : Nat.Primes, germLocalFactor w p) ≠ 0) ∧
      (∀ z : ℂ, 1 / Real.goldenRatio ^ 2 < z.re →
        ∀ᶠ w in 𝓝[≠] z, germLocalFactor w 2 ≠ 0) := by
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hhalfOne : 1 / Real.goldenRatio ^ 2 < (1 : ℂ).re := by
    simp only [Complex.one_re]
    rw [div_lt_one (sq_pos_of_pos Real.goldenRatio_pos)]
    nlinarith [Real.one_lt_goldenRatio]
  have hproductOne :
      (∏' p : Nat.Primes, germLocalFactor (1 : ℂ) p) ≠ 0 :=
    germ_product_ne_zero_of_re_ge_two_thirds (1 : ℂ) (by norm_num)
  have hlocalization : ∀ s : ℂ, 1 / Real.goldenRatio ^ 2 < s.re →
      ((∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 ↔
        germLocalFactor s 2 ≠ 0) := by
    intro s hs
    constructor
    · intro hproduct htwo
      apply hproduct
      exact tprod_of_exists_eq_zero ⟨twoPrime, by simpa [twoPrime] using htwo⟩
    · intro htwo
      apply germ_product_ne_zero_of_local_factors_ne_zero s hs
      intro p
      by_cases hp : (p : ℕ) = 2
      · have hp_eq : p = twoPrime := Nat.Primes.coe_nat_injective hp
        rw [hp_eq]
        simpa [twoPrime] using htwo
      · exact germ_local_factor_ne_zero_of_prime_ne_two s hs p hp
  have hpreconnected :
      IsPreconnected {s : ℂ | 1 / Real.goldenRatio ^ 2 < s.re} := by
    exact (convex_halfSpace_gt Complex.reLm.isLinear
      (1 / Real.goldenRatio ^ 2)).isPreconnected
  have hopen : IsOpen {s : ℂ | 1 / Real.goldenRatio ^ 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hproductIsolated : ∀ z : ℂ,
      1 / Real.goldenRatio ^ 2 < z.re →
      ∀ᶠ w in 𝓝[≠] z, (∏' p : Nat.Primes, germLocalFactor w p) ≠ 0 := by
    intro z hz
    rcases AnalyticAt.eventually_eq_zero_or_eventually_ne_zero
      (germProduct_analyticOnNhd z hz) with hzero | hisolated
    · have hall :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          germProduct_analyticOnNhd hpreconnected hz hzero
      exact (hproductOne (by simpa using hall hhalfOne)).elim
    · exact hisolated
  have hlocalIsolated : ∀ z : ℂ,
      1 / Real.goldenRatio ^ 2 < z.re →
      ∀ᶠ w in 𝓝[≠] z, germLocalFactor w 2 ≠ 0 := by
    intro z hz
    have hnearProduct := hproductIsolated z hz
    have hnearHalf :
        ∀ᶠ w in 𝓝[≠] z, 1 / Real.goldenRatio ^ 2 < w.re :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (hopen.eventually_mem hz)
    filter_upwards [hnearProduct, hnearHalf] with w hproduct hw
    exact (hlocalization w hw).mp hproduct
  exact ⟨hhalfOne, hproductOne, hlocalization, hproductIsolated,
    hlocalIsolated⟩

end

end D5.S3.Analytic.EulerGerm.GoldenGermProductZeros
