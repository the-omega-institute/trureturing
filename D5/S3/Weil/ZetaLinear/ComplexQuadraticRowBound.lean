/- GID: D5/S3/Weil/ZetaLinear/ComplexQuadraticRowBound
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   digest: Extend the existing row estimate to complex mixed forms and series. -/

import D5.S3.PrimeGaps.GreedyResidues

/-!
# Complex mixed-term row control

Library-first owner: `LongGapsBetweenPrimes.abs_quadratic_form_le_rows`.
The new theorem applies that result to coefficient norms and entry norms.
It therefore does not introduce a second real Schur-inequality proof.
The series theorem requires actual summability and actual row estimates. It
is a consumer for the zeta mixed sums; it does not assert such estimates or
claim that any zeta instance has passed the repository's admission gates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Weil.ZetaLinear.ComplexQuadraticRowBound

variable {ι : Type*} [Fintype ι]

/-- Complex coefficients, including all their cross terms, are controlled by
the absolute row sums whenever the entry norms are symmetric. -/
theorem norm_complex_quadratic_le_rows
    (a : ι → ℂ) (K : ι → ι → ℂ)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * K i j‖ ≤
      ∑ i, ‖a i‖ ^ 2 * ∑ j, ‖K i j‖ := by
  have hreal := LongGapsBetweenPrimes.abs_quadratic_form_le_rows
    (fun i => ‖a i‖) (fun i j => ‖K i j‖)
    (fun i j => by simpa only [abs_of_nonneg (norm_nonneg _)] using hsym i j)
  calc
    ‖∑ i, ∑ j, (a i * conj (a j)) * K i j‖ ≤
        ∑ i, ∑ j, ‖(a i * conj (a j)) * K i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, (‖a i‖ * ‖a j‖) * ‖K i j‖ := by
      simp only [norm_mul, Complex.norm_conj]
    _ ≤ |∑ i, ∑ j, (‖a i‖ * ‖a j‖) * ‖K i j‖| := le_abs_self _
    _ ≤ _ := by simpa only [abs_of_nonneg (norm_nonneg _)] using hreal

/-- A multiplicity- or energy-weighted row budget controls the complete form. -/
theorem norm_complex_quadratic_le_weighted_energy
    (a : ι → ℂ) (K : ι → ι → ℂ) (weight : ι → ℝ) (eta : ℝ)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, (∑ j, ‖K i j‖) ≤ eta * weight i) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * K i j‖ ≤
      eta * ∑ i, weight i * ‖a i‖ ^ 2 := by
  calc
    _ ≤ ∑ i, ‖a i‖ ^ 2 * ∑ j, ‖K i j‖ :=
      norm_complex_quadratic_le_rows a K hsym
    _ ≤ ∑ i, ‖a i‖ ^ 2 * (eta * weight i) :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Absolute summability of genuine matrix coefficients turns a row budget on
the series of norms into a uniform bound for every coefficient vector. -/
theorem norm_series_quadratic_le_weighted_energy
    (a : ι → ℂ) (term : ℕ → ι → ι → ℂ)
    (weight : ι → ℝ) (eta : ℝ)
    (hsum : ∀ i j, Summable (fun n => term n i j))
    (hsym : ∀ i j, ‖∑' n, term n i j‖ = ‖∑' n, term n j i‖)
    (hrow : ∀ i, (∑ j, ∑' n, ‖term n i j‖) ≤ eta * weight i) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * (∑' n, term n i j)‖ ≤
      eta * ∑ i, weight i * ‖a i‖ ^ 2 := by
  apply norm_complex_quadratic_le_weighted_energy a
    (fun i j => ∑' n, term n i j) weight eta hsym
  intro i
  exact (Finset.sum_le_sum fun j _ => norm_tsum_le_tsum_norm (hsum i j).norm).trans
    (hrow i)

/-- A positive weighted energy detects every nonzero coefficient vector. -/
private theorem weighted_energy_pos
    (weight : ι → ℝ) (hweight : ∀ i, 0 < weight i)
    (a : ι → ℂ) (ha : a ≠ 0) :
    0 < ∑ i, weight i * ‖a i‖ ^ 2 := by
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos' (fun j _ => mul_nonneg (hweight j).le (sq_nonneg _))
  exact ⟨i, Finset.mem_univ i, mul_pos (hweight i) (sq_pos_of_pos (norm_pos_iff.mpr hi))⟩

/-- A full complex remainder with a row budget below the diagonal margin
preserves negative definiteness on the whole coefficient space. -/
theorem negative_margin_of_complex_rows
    (K : ι → ι → ℂ) (weight : ι → ℝ) (margin eta : ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, (∑ j, ‖K i j‖) ≤ eta * weight i)
    (hmargin : eta < margin) (a : ι → ℂ) (ha : a ≠ 0) :
    -margin * (∑ i, weight i * ‖a i‖ ^ 2) +
      (∑ i, ∑ j, (a i * conj (a j)) * K i j).re < 0 := by
  have he := weighted_energy_pos weight hweight a ha
  have hr := (Complex.re_le_norm _).trans
    (norm_complex_quadratic_le_weighted_energy a K weight eta hsym hrow)
  nlinarith

/-- The same proved row control also preserves a positive margin, the sign
needed for a sieve-functional threshold certificate. -/
theorem positive_margin_of_complex_rows
    (K : ι → ι → ℂ) (weight : ι → ℝ) (margin eta : ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, (∑ j, ‖K i j‖) ≤ eta * weight i)
    (hmargin : eta < margin) (a : ι → ℂ) (ha : a ≠ 0) :
    0 < margin * (∑ i, weight i * ‖a i‖ ^ 2) +
      (∑ i, ∑ j, (a i * conj (a j)) * K i j).re := by
  have he := weighted_energy_pos weight hweight a ha
  have hn := norm_complex_quadratic_le_weighted_energy a K weight eta hsym hrow
  have hr := (Complex.abs_re_le_norm (∑ i, ∑ j, (a i * conj (a j)) * K i j)).trans hn
  have hl := (abs_le.mp hr).1
  nlinarith

#print axioms norm_complex_quadratic_le_rows
#print axioms norm_series_quadratic_le_weighted_energy
#print axioms negative_margin_of_complex_rows
#print axioms positive_margin_of_complex_rows

end D5.S3.Weil.ZetaLinear.ComplexQuadraticRowBound
