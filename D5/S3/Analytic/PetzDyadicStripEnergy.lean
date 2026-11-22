/- GID: D5/S3/Analytic/PetzDyadicStripEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzDyadicStripEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The strip energy splits into finite dyadic logistic energies and a scaled tail. -/

import D5.S3.Analytic.PetzStripGramRemainder

/-! # Dyadic decomposition of the Petz strip energy -/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace PetzDyadicStripEnergy

open PetzStripGramRemainder (stripGram logistic remainder remainder_quadratic_nonneg)
open ExponentialGramWeightedEvaluation (exponentialSum frequency)
open PetzExponentialBoundaryEvaluation (petzWeight petzWeight_pos)
open private cothFactor energy_integral logistic_gram_entry verticalExponential from
  D5.S3.Analytic.PetzStripGramRemainder
open private coth_half_sub_coth from D5.S3.Analytic.PetzStripFiniteSeries

noncomputable section

private theorem half_kernel (d : ℝ) :
    logistic (d / 2) = Real.cosh (d / 4) * logistic d ∧
      2 * cothFactor (d / 2) - cothFactor d = logistic d := by
  by_cases hd : d = 0
  · norm_num [hd, logistic, cothFactor]
  have hd' : d / 2 ≠ 0 := div_ne_zero hd (by norm_num)
  have hs : Real.sinh (d / 4) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero hd (by norm_num))
  have hc : Real.cosh (d / 4) ≠ 0 := (Real.cosh_pos _).ne'
  have hhalf : d / 2 / 2 = d / 4 := by ring
  have hsh : Real.sinh (d / 2) = 2 * Real.sinh (d / 4) * Real.cosh (d / 4) := by
    rw [← Real.sinh_two_mul]
    congr 1
    ring
  constructor
  · simp only [logistic, ite_eq_right hd, ite_eq_right hd', hhalf, hsh]
    field_simp [hs, hc]
    ring
  · simp only [logistic, cothFactor, ite_eq_right hd, ite_eq_right hd', hhalf]
    have h := coth_half_sub_coth hd'
    rw [hhalf] at h
    linear_combination (d / 2) * h

private theorem exp_half_add (x y : ℝ) :
    2 * (Real.exp (x / 4) * Real.exp (y / 4)) * Real.cosh ((y - x) / 4) =
      Real.exp (x / 2) + Real.exp (y / 2) := by
  rw [Real.cosh_eq]
  calc
    _ = Real.exp (x / 4 + y / 4 + (y - x) / 4) +
        Real.exp (x / 4 + y / 4 + -((y - x) / 4)) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by
      rw [show x / 4 + y / 4 + (y - x) / 4 = y / 2 by ring,
        show x / 4 + y / 4 + -((y - x) / 4) = x / 2 by ring, add_comm]

/-- The remainder of the logistic jump is twice the strip Gram at half frequency. -/
theorem remainder_eq_two_mul_stripGram_half (x y : ℝ) :
    remainder x y = 2 * stripGram (x / 2) (y / 2) := by
  obtain ⟨hlog, hcoth⟩ := half_kernel (y - x)
  unfold remainder stripGram
  rw [show y / 2 - x / 2 = (y - x) / 2 by ring,
    show x / 2 / 2 = x / 4 by ring, show y / 2 / 2 = y / 4 by ring, hlog]
  linear_combination
    -(exp_half_add x y) * logistic (y - x) + hcoth

variable {ι : Type*} [Fintype ι]

/-- The real quadratic energy of the exact strip Gram. -/
def stripEnergy (x : ι → ℝ) (c : ι → ℂ) : ℝ :=
  (∑ i, ∑ j, (star (c i) * c j) * (stripGram (x i) (x j) : ℂ)).re

private def jumpCoefficients (x : ι → ℝ) (c : ι → ℂ) (i : ι) : ℂ :=
  c i * (1 - (Real.exp (x i / 2) : ℂ))

/-- The logistic-weighted squared norm of the upper-minus-lower boundary amplitude. -/
def logisticEnergy (x : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ t : ℝ, petzWeight t * ‖exponentialSum x (jumpCoefficients x c) (t : ℂ)‖ ^ 2

private theorem logisticEnergy_eq_quadratic (x : ι → ℝ) (c : ι → ℂ) :
    (logisticEnergy x c : ℂ) =
      ∑ i, ∑ j, (star (c i) * c j) *
        (((1 - Real.exp (x i / 2)) * (1 - Real.exp (x j / 2)) * logistic (x j - x i) : ℝ) : ℂ) := by
  have h := energy_integral (jumpCoefficients x c) (fun i => verticalExponential 0 (x i))
    PetzLogisticMidline.upperWeight (fun i j => (logistic_gram_entry (x i) (x j)).1)
  have hexp (t : ℝ) :
      exponentialSum x (jumpCoefficients x c) (t : ℂ) =
        ∑ i, jumpCoefficients x c i * verticalExponential 0 (x i) t := by
    simp only [exponentialSum, frequency, verticalExponential, PetzLogisticMidline.line,
      Complex.ofReal_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_rotate Complex.I, mul_assoc (x i : ℂ)]
  unfold logisticEnergy
  simp_rw [hexp]
  change ((∫ t : ℝ, PetzLogisticMidline.upperWeight t *
    ‖∑ i, jumpCoefficients x c i * verticalExponential 0 (x i) t‖ ^ 2 : ℝ) : ℂ) = _
  rw [h.2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [(logistic_gram_entry (x i) (x j)).2]
  simp only [jumpCoefficients, star_mul, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

private theorem remainderEnergy_eq (x : ι → ℝ) (c : ι → ℂ) :
    (∑ i, ∑ j, (star (c i) * c j) * (remainder (x i) (x j) : ℂ)).re =
      2 * stripEnergy (fun i => x i / 2) c := by
  unfold stripEnergy
  simp_rw [remainder_eq_two_mul_stripGram_half, Complex.ofReal_mul, Complex.ofReal_ofNat,
    show ∀ a b : ℂ, a * (2 * b) = 2 * (a * b) by intro a b; ring, ← Finset.mul_sum]
  simp

private theorem stripEnergy_step (x : ι → ℝ) (c : ι → ℂ) :
    stripEnergy x c = logisticEnergy x c + 2 * stripEnergy (fun i => x i / 2) c := by
  rw [← remainderEnergy_eq x c, ← Complex.ofReal_re (logisticEnergy x c)]
  simp only [logisticEnergy_eq_quadratic, stripEnergy, remainder, Complex.ofReal_sub, mul_sub,
    Finset.sum_sub_distrib, Complex.sub_re]
  ring

private theorem stripEnergy_nonneg (x : ι → ℝ) (c : ι → ℂ) : 0 ≤ stripEnergy x c := by
  have h := remainder_quadratic_nonneg (fun i => 2 * x i) c
  rw [remainderEnergy_eq, show (fun i => 2 * x i / 2) = x by funext i; ring] at h
  linarith

private theorem logisticEnergy_nonneg (x : ι → ℝ) (c : ι → ℂ) : 0 ≤ logisticEnergy x c :=
  integral_nonneg fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _)

/-- The exact strip energy is the sum of the first M dyadic logistic energies
and the strip energy of the remaining scaled family, with its exact weight. -/
theorem stripEnergy_dyadic (x : ι → ℝ) (c : ι → ℂ) (M : ℕ) :
    stripEnergy x c =
      (∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c) +
        (2 : ℝ) ^ M * stripEnergy (fun i => x i / 2 ^ M) c := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ (2 : ℝ) M,
      stripEnergy_step (fun i => x i / 2 ^ M) c]
    simp_rw [div_mul_eq_div_div]
    ring

/-- At every finite cutoff the partial dyadic sum is nonnegative and bounded by
the original strip energy. -/
theorem stripEnergy_dyadic_lower_bound (x : ι → ℝ) (c : ι → ℂ) (M : ℕ) :
    0 ≤ ∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c ∧
      (∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c) ≤
        stripEnergy x c := by
  constructor
  · exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (logisticEnergy_nonneg _ c)
  · rw [stripEnergy_dyadic x c M]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (stripEnergy_nonneg _ c))

#print axioms stripEnergy
#print axioms logisticEnergy
#print axioms remainder_eq_two_mul_stripGram_half
#print axioms stripEnergy_dyadic
#print axioms stripEnergy_dyadic_lower_bound

end

end PetzDyadicStripEnergy
