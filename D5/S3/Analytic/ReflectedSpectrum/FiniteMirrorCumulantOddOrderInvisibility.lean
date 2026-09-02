/- GID: D5/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite mirror windows cancel odd transverse moments and preserve even ones. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum

/- Library-search audit trail (2026-09-03):
   * Repository search found the exact reflected exponential pair in
     `ReflectedGrowthPairNegativeSquare` and its arbitrary-order derivative in
     `ReflectedGrowthPairSecondOrderSpectrum`; both are imported and reused.
   * Pinned Mathlib supplies `iteratedDeriv_fun_sum`,
     `iteratedDeriv_const_mul_field`, `Odd.neg_pow`, and `Even.neg_pow`.
   * Loogle returned no exact whole-statement hit; LeanSearch returned no hit;
     unauthenticated GitHub code search returned HTTP 401.
   * The source defines this finite weighted moment-generating function locally
     in lines 1893-1905. No Riemann-hypothesis premise or external definition
     chain is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ReflectedSpectrum.FiniteMirrorCumulantOddOrderInvisibility

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum

/-- The transverse moment-generating function of the finite mirror window.
This is the formula given in source lines 1893-1905, with `representatives`
indexing the chosen right representatives, `multiplicity` carrying `m_a`,
`weight` carrying `w_a`, and `displacement` carrying `delta_a`. -/
def transverseMomentGeneratingFunction {ι : Type*}
    (representatives : Finset ι) (multiplicity : ι → ℕ)
    (weight displacement : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ a ∈ representatives,
    (multiplicity a : ℝ) * weight a * reflectedGrowthSum (displacement a) u

/-- In a finite mirror-closed zero window, every odd centered derivative of
the source-defined transverse moment-generating function vanishes. Pairwise,
all odd displacement powers cancel while all even displacement powers add.
The standing hypotheses `weightPositive` and `displacementNonnegative` are the
positive-weight and right-representative conditions in source lines 1883-1891. -/
theorem finite_mirror_cumulant_odd_order_invisibility {ι : Type*}
    (representatives : Finset ι) (multiplicity : ι → ℕ)
    (weight displacement : ι → ℝ)
    (_weightPositive : ∀ a ∈ representatives, 0 < weight a)
    (_displacementNonnegative : ∀ a ∈ representatives, 0 ≤ displacement a) :
    (∀ r : ℕ,
      iteratedDeriv (2 * r + 1)
        (transverseMomentGeneratingFunction
          representatives multiplicity weight displacement) 0 = 0) ∧
    (∀ a ∈ representatives, ∀ r : ℕ,
      displacement a ^ (2 * r + 1) + (-displacement a) ^ (2 * r + 1) = 0) ∧
    (∀ a ∈ representatives, ∀ r : ℕ,
      displacement a ^ (2 * r) + (-displacement a) ^ (2 * r) =
        2 * displacement a ^ (2 * r)) := by
  have oddPowerCancellation : ∀ a ∈ representatives, ∀ r : ℕ,
      displacement a ^ (2 * r + 1) + (-displacement a) ^ (2 * r + 1) = 0 := by
    intro a _ r
    rw [Odd.neg_pow (⟨r, rfl⟩ : Odd (2 * r + 1))]
    ring
  have evenPowerAddition : ∀ a ∈ representatives, ∀ r : ℕ,
      displacement a ^ (2 * r) + (-displacement a) ^ (2 * r) =
        2 * displacement a ^ (2 * r) := by
    intro a _ r
    rw [Even.neg_pow (⟨r, by omega⟩ : Even (2 * r))]
    ring
  refine ⟨?_, oddPowerCancellation, evenPowerAddition⟩
  intro r
  unfold transverseMomentGeneratingFunction
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_eq_zero
    intro a ha
    rw [iteratedDeriv_const_mul_field,
      reflected_growth_sum_iterated_derivative]
    simp only [positiveRateBranch, negativeRateBranch, reflectedGrowthPair,
      mul_zero, neg_zero, Real.exp_zero, mul_one]
    rw [oddPowerCancellation a ha r, mul_zero]
  · intro a ha
    unfold reflectedGrowthSum reflectedGrowthPair
    fun_prop

/-- Reverse probe for CAS assertion A1: the public theorem itself entails each
specified odd centered derivative, without unfolding its proof. -/
example {ι : Type*} (representatives : Finset ι) (multiplicity : ι → ℕ)
    (weight displacement : ι → ℝ)
    (weightPositive : ∀ a ∈ representatives, 0 < weight a)
    (displacementNonnegative : ∀ a ∈ representatives, 0 ≤ displacement a)
    (r : ℕ) :
    iteratedDeriv (2 * r + 1)
      (transverseMomentGeneratingFunction
        representatives multiplicity weight displacement) 0 = 0 := by
  exact
    (finite_mirror_cumulant_odd_order_invisibility representatives multiplicity
      weight displacement weightPositive displacementNonnegative).1 r

/-- Separation probe for CAS assertions A2 and A3: at a nonzero displacement,
the odd mirror pair cancels while the even mirror pair has value two. -/
example (r : ℕ) :
    (1 : ℝ) ^ (2 * r + 1) + (-1 : ℝ) ^ (2 * r + 1) = 0 ∧
    (1 : ℝ) ^ (2 * r) + (-1 : ℝ) ^ (2 * r) = 2 := by
  have law :=
    finite_mirror_cumulant_odd_order_invisibility ({()} : Finset Unit)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  constructor
  · simpa using law.2.1 () (by simp) r
  · simpa using law.2.2 () (by simp) r

#print axioms finite_mirror_cumulant_odd_order_invisibility

end D5.S3.Analytic.ReflectedSpectrum.FiniteMirrorCumulantOddOrderInvisibility
