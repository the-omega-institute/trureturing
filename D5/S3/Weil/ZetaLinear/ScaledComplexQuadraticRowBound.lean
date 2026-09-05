/- GID: D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   digest: Certify full complex mixed forms by positive scaled rows and retain weighted margins. -/

import D5.S3.Weil.ZetaLinear.ComplexQuadraticRowBound

/-!
# Positive diagonal scaling for complex mixed-form certificates

The real row estimate remains owned by
`LongGapsBetweenPrimes.abs_quadratic_form_le_rows`.
We apply it to `norm (a i) / p i` and `p i * p j * norm (K i j)`.
The positive vector `p` is a mathematical Schur witness, not an information
score, a change of object arena, or an asserted zeta analytic bound.

Absolute summability, envelope inequalities, and actual matrix norm symmetry
remain explicit inputs. These results do not assert those inputs for the
parallel Burnol packet implementation. The two-channel regression is exact
finite algebra and is not a model of actual zeta zeros.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Weil.ZetaLinear.ScaledComplexQuadraticRowBound

open D5.S3.Weil.ZetaLinear.ComplexQuadraticRowBound

variable {ι : Type*} [Fintype ι]

/-- Positive scaled row inequalities control every complex coefficient vector.
The energy weights are retained individually, rather than replaced by a floor. -/
theorem norm_complex_quadratic_le_scaled_rows
    (a : ι → ℂ) (K : ι → ι → ℂ) (weight p : ι → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < p i)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, (∑ j, ‖K i j‖ * p j) ≤ eta * weight i * p i) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * K i j‖ ≤
      eta * ∑ i, weight i * ‖a i‖ ^ 2 := by
  have hp0 (i : ι) : p i ≠ 0 := ne_of_gt (hp i)
  have hnonneg (i j : ι) : 0 ≤ p i * p j * ‖K i j‖ :=
    mul_nonneg (mul_nonneg (hp i).le (hp j).le) (norm_nonneg _)
  have hreal := LongGapsBetweenPrimes.abs_quadratic_form_le_rows
    (fun i => ‖a i‖ / p i) (fun i j => p i * p j * ‖K i j‖)
    (fun i j => by
      rw [abs_of_nonneg (hnonneg i j), abs_of_nonneg (hnonneg j i), hsym i j]
      ring)
  calc
    _ ≤ ∑ i, ∑ j, ‖(a i * conj (a j)) * K i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, (‖a i‖ * ‖a j‖) * ‖K i j‖ := by
      simp only [norm_mul, Complex.norm_conj]
    _ = ∑ i, ∑ j, (‖a i‖ / p i) * (‖a j‖ / p j) *
        (p i * p j * ‖K i j‖) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      field_simp [hp0 i, hp0 j] <;> ring
    _ ≤ |∑ i, ∑ j, (‖a i‖ / p i) * (‖a j‖ / p j) *
        (p i * p j * ‖K i j‖)| := le_abs_self _
    _ ≤ ∑ i, (‖a i‖ / p i) ^ 2 * ∑ j, |p i * p j * ‖K i j‖| := hreal
    _ = ∑ i, (‖a i‖ / p i) ^ 2 * (p i * ∑ j, ‖K i j‖ * p j) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (hnonneg i j)]
      ring
    _ ≤ ∑ i, (‖a i‖ / p i) ^ 2 * (p i * (eta * weight i * p i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hrow i) (hp i).le) (sq_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hp0 i] <;> ring

/-- A scaled budget for absolutely convergent matrix coefficients controls the
complete series form. Symmetry is required only after the series is summed. -/
theorem norm_series_quadratic_le_scaled_rows
    (a : ι → ℂ) (term : ℕ → ι → ι → ℂ)
    (weight p : ι → ℝ) (eta : ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∀ i j, Summable (fun n => ‖term n i j‖))
    (hsym : ∀ i j, ‖∑' n, term n i j‖ = ‖∑' n, term n j i‖)
    (hrow : ∀ i, (∑ j, (∑' n, ‖term n i j‖) * p j) ≤
      eta * weight i * p i) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * (∑' n, term n i j)‖ ≤
      eta * ∑ i, weight i * ‖a i‖ ^ 2 := by
  apply norm_complex_quadratic_le_scaled_rows a
    (fun i j => ∑' n, term n i j) weight p eta hp hsym
  intro i
  exact (Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (hsum i j)) (hp j).le).trans
      (hrow i)

/-- A fixed matrix envelope produces a coefficient-uniform geometric bound.
No scalar total over all matrix entries needs to replace the scaled rows. -/
theorem geometric_matrix_envelope_bound
    (K : ℕ → ι → ι → ℂ) (B : ι → ι → ℝ)
    (weight p : ι → ℝ) (lambda : ℝ) (hp : ∀ i, 0 < p i)
    (hsym : ∀ N i j, ‖K N i j‖ = ‖K N j i‖)
    (hentry : ∀ N i j, ‖K N i j‖ ≤ (1 / 4 : ℝ) ^ (N + 1) * B i j)
    (hrow : ∀ i, (∑ j, B i j * p j) ≤ lambda * weight i * p i)
    (N : ℕ) (a : ι → ℂ) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * K N i j‖ ≤
      ((1 / 4 : ℝ) ^ (N + 1) * lambda) * ∑ i, weight i * ‖a i‖ ^ 2 := by
  apply norm_complex_quadratic_le_scaled_rows a (K N) weight p
    ((1 / 4 : ℝ) ^ (N + 1) * lambda) hp (hsym N)
  intro i
  calc
    _ ≤ ∑ j, ((1 / 4 : ℝ) ^ (N + 1) * B i j) * p j :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hentry N i j) (hp j).le
    _ = (1 / 4 : ℝ) ^ (N + 1) * ∑ j, B i j * p j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (1 / 4 : ℝ) ^ (N + 1) * (lambda * weight i * p i) :=
      mul_le_mul_of_nonneg_left (hrow i) (pow_nonneg (by norm_num) _)
    _ = _ := by ring

/-- A separate complex perturbation consumes its own explicit weighted budget.
The conclusion keeps the remaining coercive margin for every vector. -/
theorem scaled_rows_robust_coercive_bound
    (a : ι → ℂ) (K : ι → ι → ℂ) (weight p : ι → ℝ)
    (margin eta tau : ℝ) (err : ℂ) (hp : ∀ i, 0 < p i)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, (∑ j, ‖K i j‖ * p j) ≤ eta * weight i * p i)
    (herr : ‖err‖ ≤ tau * ∑ i, weight i * ‖a i‖ ^ 2) :
    -margin * (∑ i, weight i * ‖a i‖ ^ 2) +
      ((∑ i, ∑ j, (a i * conj (a j)) * K i j) + err).re ≤
        -(margin - eta - tau) * ∑ i, weight i * ‖a i‖ ^ 2 := by
  have hk := (Complex.re_le_norm _).trans
    (norm_complex_quadratic_le_scaled_rows a K weight p eta hp hsym hrow)
  have he := (Complex.re_le_norm err).trans herr
  rw [Complex.add_re]
  nlinarith

/-- A positive residual margin gives strict negativity on the entire nonzero
coefficient space, including independent perturbations within their budget. -/
theorem scaled_rows_robust_strict_negativity
    (a : ι → ℂ) (K : ι → ι → ℂ) (weight p : ι → ℝ)
    (margin eta tau : ℝ) (err : ℂ)
    (hweight : ∀ i, 0 < weight i) (hp : ∀ i, 0 < p i)
    (hsym : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, (∑ j, ‖K i j‖ * p j) ≤ eta * weight i * p i)
    (herr : ‖err‖ ≤ tau * ∑ i, weight i * ‖a i‖ ^ 2)
    (hmargin : eta + tau < margin) (ha : a ≠ 0) :
    -margin * (∑ i, weight i * ‖a i‖ ^ 2) +
      ((∑ i, ∑ j, (a i * conj (a j)) * K i j) + err).re < 0 := by
  have hpos := weighted_energy_pos weight hweight a ha
  have hgap : 0 < margin - eta - tau := by linarith
  exact (scaled_rows_robust_coercive_bound a K weight p margin eta tau err
    hp hsym hrow herr).trans_lt
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hgap) hpos)

/-- For two positive-coupled channels the existence of a strict positive
scaling is exactly the determinant threshold. A midpoint supplies the witness. -/
theorem two_channel_scaling_iff (r d0 d1 : ℝ) (hr : 0 < r) (hd1 : 0 < d1) :
    (∃ t : ℝ, 0 < t ∧ r * t < d0 ∧ r / t < d1) ↔ r ^ 2 < d0 * d1 := by
  constructor
  · rintro ⟨t, ht, h0, h1⟩
    have h1' : r < d1 * t := (div_lt_iff₀ ht).mp h1
    have hl := mul_lt_mul_of_pos_left h1' hr
    have hu := mul_lt_mul_of_pos_right h0 hd1
    nlinarith
  · intro hdisc
    have hinterval : r / d1 < d0 / r :=
      (div_lt_div_iff₀ hd1 hr).mpr (by nlinarith)
    let t : ℝ := (r / d1 + d0 / r) / 2
    have hlo : r / d1 < t := by dsimp [t]; linarith
    have hhi : t < d0 / r := by dsimp [t]; linarith
    have ht : 0 < t := (div_pos hr hd1).trans hlo
    refine ⟨t, ht, ?_, ?_⟩
    · have h := (lt_div_iff₀ hr).mp hhi
      nlinarith
    · apply (div_lt_iff₀ ht).mpr
      have h := (div_lt_iff₀ hd1).mp hlo
      nlinarith

/-- Exact regression: the scaled certificate proves negativity although no
unscaled row budget below one is possible for the same matrix and energy. -/
theorem two_channel_scaled_regression :
    (∀ a : Fin 2 → ℂ, a ≠ 0 →
      -(∑ i, (if i = 0 then (1 : ℝ) else 9) * ‖a i‖ ^ 2) +
        (∑ i, ∑ j, (a i * conj (a j)) *
          (if i = j then (0 : ℂ) else 2)).re < 0) ∧
    ¬ ∃ eta : ℝ, eta < 1 ∧ ∀ i : Fin 2,
      (∑ j : Fin 2, ‖if i = j then (0 : ℂ) else 2‖) ≤
        eta * (if i = 0 then (1 : ℝ) else 9) := by
  constructor
  · intro a ha
    have h := scaled_rows_robust_strict_negativity a
      (fun i j => if i = j then (0 : ℂ) else 2)
      (fun i => if i = 0 then (1 : ℝ) else 9)
      (fun i => if i = 0 then (3 : ℝ) else 1)
      1 (2 / 3) 0 0
      (by intro i; fin_cases i <;> norm_num)
      (by intro i; fin_cases i <;> norm_num)
      (by intro i j; simp only [eq_comm])
      (by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two])
      (by simp) (by norm_num) ha
    simpa using h
  · rintro ⟨eta, hlt, hrow⟩
    have h0 := hrow 0
    norm_num [Fin.sum_univ_two] at h0
    linarith

#print axioms norm_complex_quadratic_le_scaled_rows
#print axioms norm_series_quadratic_le_scaled_rows
#print axioms geometric_matrix_envelope_bound
#print axioms scaled_rows_robust_coercive_bound
#print axioms scaled_rows_robust_strict_negativity
#print axioms two_channel_scaling_iff
#print axioms two_channel_scaled_regression

end D5.S3.Weil.ZetaLinear.ScaledComplexQuadraticRowBound
