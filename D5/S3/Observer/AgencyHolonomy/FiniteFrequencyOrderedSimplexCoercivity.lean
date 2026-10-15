/- GID: D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite nonresonant frequency family has a uniform ordered-simplex energy bound.
   -/

import D5.S3.Observer.AgencyHolonomy.OrderedTimeSimplexSecondMagnusAverage
import Mathlib.Tactic

/-!
# Finite-frequency ordered-simplex coercivity

The exact ordered-simplex response gives a common-window estimate for a finite
family once its frequency gaps are separated from zero.  This module records
that estimate for arbitrary real coefficients.  It is a finite analytic
interface only: no infinite-family limit, Weil test construction, or zero
location statement is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Observer.AgencyHolonomy.FiniteFrequencyOrderedSimplexCoercivity

open D5.S3.Observer.AgencyHolonomy.OrderedTimeSimplexSecondMagnusAverage

universe u

/-- The finite family energy obtained by weighting each ordered-simplex
response by a squared real coefficient. -/
noncomputable def finiteOrderedSimplexEnergy
    {ι : Type u} [Fintype ι]
    (gap coefficient : ι → ℝ) (horizon : ℝ) : ℝ :=
  ∑ i, orderedTimeSimplexKernelAverage (gap i) horizon * (coefficient i) ^ 2

/-- The same ordered-simplex response for complex Fourier coefficients. -/
noncomputable def finiteComplexOrderedSimplexEnergy
    {ι : Type u} [Fintype ι]
    (gap : ι → ℝ) (coefficient : ι → ℂ) (horizon : ℝ) : ℝ :=
  ∑ i, orderedTimeSimplexKernelAverage (gap i) horizon *
    Complex.normSq (coefficient i)

private theorem gap_sq_pos
    (gap δ : ℝ) (hδ : 0 < δ) (hGap : δ ≤ |gap|) :
    0 < gap ^ 2 := by
  have hGapNe : gap ≠ 0 := by
    intro hZero
    subst gap
    have hZeroGap : δ ≤ 0 := by simpa using hGap
    exact (not_le_of_gt hδ) hZeroGap
  positivity

private theorem gap_sq_lower
    (gap δ : ℝ) (hδ : 0 < δ) (hGap : δ ≤ |gap|) :
    δ ^ 2 ≤ gap ^ 2 := by
  have hδ' : 0 ≤ δ := le_of_lt hδ
  have hAbsSq : δ ^ 2 ≤ |gap| ^ 2 :=
    (sq_le_sq₀ hδ' (abs_nonneg gap)).2 hGap
  simpa only [sq_abs] using hAbsSq

private theorem ordered_simplex_pointwise_lower
    (gap horizon δ : ℝ) (hδ : 0 < δ) (hGap : δ ≤ |gap|) :
    horizon ^ 2 - 4 / δ ^ 2 ≤
      orderedTimeSimplexKernelAverage gap horizon := by
  have hGapNe : gap ≠ 0 := by
    intro hZero
    subst gap
    have hZeroGap : δ ≤ 0 := by simpa using hGap
    exact (not_le_of_gt hδ) hZeroGap
  have hGapSq : 0 < gap ^ 2 := gap_sq_pos gap δ hδ hGap
  have hDeltaSq : 0 < δ ^ 2 := by positivity
  have hSq : δ ^ 2 ≤ gap ^ 2 := gap_sq_lower gap δ hδ hGap
  have hInv : 1 / gap ^ 2 ≤ 1 / δ ^ 2 :=
    one_div_le_one_div_of_le hDeltaSq hSq
  have hCosLower : 0 ≤ 1 - Real.cos (gap * horizon) := by
    nlinarith [Real.cos_le_one (gap * horizon)]
  have hCosUpper : 1 - Real.cos (gap * horizon) ≤ 2 := by
    nlinarith [Real.neg_one_le_cos (gap * horizon)]
  have hFraction :
      (1 - Real.cos (gap * horizon)) / gap ^ 2 ≤ 2 / δ ^ 2 := by
    have hFirst :
        (1 - Real.cos (gap * horizon)) / gap ^ 2 ≤ 2 / gap ^ 2 := by
      exact div_le_div_of_nonneg_right hCosUpper (le_of_lt hGapSq)
    have hSecond : 2 / gap ^ 2 ≤ 2 / δ ^ 2 := by
      calc
        2 / gap ^ 2 = 2 * (1 / gap ^ 2) := by ring
        _ ≤ 2 * (1 / δ ^ 2) :=
          mul_le_mul_of_nonneg_left hInv (by norm_num)
        _ = 2 / δ ^ 2 := by ring
    exact hFirst.trans hSecond
  have hScaled :
      2 * ((1 - Real.cos (gap * horizon)) / gap ^ 2) ≤
        4 / δ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hFraction (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * ((1 - Real.cos (gap * horizon)) / gap ^ 2) ≤
          2 * (2 / δ ^ 2) := h
      _ = 4 / δ ^ 2 := by ring
  rw [ordered_time_simplex_kernel_average_formula gap horizon hGapNe]
  calc
    horizon ^ 2 - 4 / δ ^ 2 ≤
        horizon ^ 2 - 2 * ((1 - Real.cos (gap * horizon)) / gap ^ 2) := by
      linarith
    _ = horizon ^ 2 -
        2 * (1 - Real.cos (gap * horizon)) / gap ^ 2 := by ring

private theorem ordered_simplex_pointwise_upper
    (gap horizon δ : ℝ) (hδ : 0 < δ) (hGap : δ ≤ |gap|) :
    orderedTimeSimplexKernelAverage gap horizon ≤ horizon ^ 2 := by
  have hGapNe : gap ≠ 0 := by
    intro hZero
    subst gap
    have hZeroGap : δ ≤ 0 := by simpa using hGap
    exact (not_le_of_gt hδ) hZeroGap
  have hGapSq : 0 < gap ^ 2 := gap_sq_pos gap δ hδ hGap
  have hCosLower : 0 ≤ 1 - Real.cos (gap * horizon) := by
    nlinarith [Real.cos_le_one (gap * horizon)]
  rw [ordered_time_simplex_kernel_average_formula gap horizon hGapNe]
  have hFraction : 0 ≤ 2 * (1 - Real.cos (gap * horizon)) / gap ^ 2 := by
    positivity
  linarith

/-- A finite family with gap floor `δ` is controlled from below by the
uniform scalar response floor. -/
theorem finite_ordered_simplex_energy_lower_bound
    {ι : Type u} [Fintype ι]
    (gap coefficient : ι → ℝ) (horizon δ : ℝ)
    (hδ : 0 < δ) (hGap : ∀ i, δ ≤ |gap i|) :
    (horizon ^ 2 - 4 / δ ^ 2) * (∑ i, (coefficient i) ^ 2) ≤
      finiteOrderedSimplexEnergy gap coefficient horizon := by
  classical
  unfold finiteOrderedSimplexEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    exact mul_le_mul_of_nonneg_right
      (ordered_simplex_pointwise_lower (gap i) horizon δ hδ (hGap i))
      (sq_nonneg (coefficient i))

/-- The same finite family has the trivial sharp upper envelope `horizon²`. -/
theorem finite_ordered_simplex_energy_upper_bound
    {ι : Type u} [Fintype ι]
    (gap coefficient : ι → ℝ) (horizon δ : ℝ)
    (hδ : 0 < δ) (hGap : ∀ i, δ ≤ |gap i|) :
    finiteOrderedSimplexEnergy gap coefficient horizon ≤
      horizon ^ 2 * (∑ i, (coefficient i) ^ 2) := by
  classical
  unfold finiteOrderedSimplexEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    exact mul_le_mul_of_nonneg_right
      (ordered_simplex_pointwise_upper (gap i) horizon δ hδ (hGap i))
      (sq_nonneg (coefficient i))

/-- A finite nonresonant family has the same common-window lower bound for
complex coefficients, with squared modulus as the coefficient energy. -/
theorem finite_complex_ordered_simplex_energy_lower_bound
    {ι : Type u} [Fintype ι]
    (gap : ι → ℝ) (coefficient : ι → ℂ) (horizon δ : ℝ)
    (hδ : 0 < δ) (hGap : ∀ i, δ ≤ |gap i|) :
    (horizon ^ 2 - 4 / δ ^ 2) *
        (∑ i, Complex.normSq (coefficient i)) ≤
      finiteComplexOrderedSimplexEnergy gap coefficient horizon := by
  classical
  unfold finiteComplexOrderedSimplexEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    exact mul_le_mul_of_nonneg_right
      (ordered_simplex_pointwise_lower (gap i) horizon δ hδ (hGap i))
      (Complex.normSq_nonneg _)

/-- The complex-coefficient energy has the same horizon-squared upper envelope. -/
theorem finite_complex_ordered_simplex_energy_upper_bound
    {ι : Type u} [Fintype ι]
    (gap : ι → ℝ) (coefficient : ι → ℂ) (horizon δ : ℝ)
    (hδ : 0 < δ) (hGap : ∀ i, δ ≤ |gap i|) :
    finiteComplexOrderedSimplexEnergy gap coefficient horizon ≤
      horizon ^ 2 * (∑ i, Complex.normSq (coefficient i)) := by
  classical
  unfold finiteComplexOrderedSimplexEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    exact mul_le_mul_of_nonneg_right
      (ordered_simplex_pointwise_upper (gap i) horizon δ hδ (hGap i))
      (Complex.normSq_nonneg _)

/-- Multiplying each coefficient by a unit complex phase preserves the finite
ordered-simplex energy. -/
theorem finite_complex_ordered_simplex_energy_phase_invariant
    {ι : Type u} [Fintype ι]
    (gap : ι → ℝ) (coefficient phase : ι → ℂ) (horizon : ℝ)
    (hPhase : ∀ i, Complex.normSq (phase i) = 1) :
    finiteComplexOrderedSimplexEnergy gap
        (fun i => phase i * coefficient i) horizon =
      finiteComplexOrderedSimplexEnergy gap coefficient horizon := by
  classical
  unfold finiteComplexOrderedSimplexEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_mul, hPhase i, one_mul]

/-- The lower coercivity constant is positive once the common horizon exceeds
the worst half-turn scale. -/
theorem ordered_simplex_coercivity_constant_pos
    (horizon δ : ℝ) (hδ : 0 < δ) (hWindow : 2 / δ < horizon) :
    0 < horizon ^ 2 - 4 / δ ^ 2 := by
  have hScale : 0 < 2 / δ := by positivity
  have hSquare : (2 / δ) ^ 2 = 4 / δ ^ 2 := by
    field_simp
    norm_num
  rw [← hSquare]
  nlinarith [sq_nonneg (horizon - 2 / δ)]

#print axioms finite_ordered_simplex_energy_lower_bound
#print axioms finite_ordered_simplex_energy_upper_bound
#print axioms finite_complex_ordered_simplex_energy_lower_bound
#print axioms finite_complex_ordered_simplex_energy_upper_bound
#print axioms finite_complex_ordered_simplex_energy_phase_invariant
#print axioms ordered_simplex_coercivity_constant_pos

end D5.S3.Observer.AgencyHolonomy.FiniteFrequencyOrderedSimplexCoercivity
