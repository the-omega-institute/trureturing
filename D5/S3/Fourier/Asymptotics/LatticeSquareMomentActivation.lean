/- GID: D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/LatticeSquareMomentActivation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact support thresholds for the integer-lattice squared-mass minimizer. -/

import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-! Exact support activation for minimum squared mass under a second-moment budget on ℤ. -/

open Finset

noncomputable section

namespace D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

set_option autoImplicit false

private def latticeInterval (n : ℕ) : Finset ℤ :=
  Icc (-(n : ℤ)) (n : ℤ)

private theorem sum_latticeInterval_even (n : ℕ) (f : ℤ → ℝ)
    (hzero : f 0 = 0) (heven : ∀ k, f (-k) = f k) :
    (∑ k ∈ latticeInterval n, f k) = 2 * ∑ j ∈ range (n + 1), f (j : ℤ) := by
  induction n with
  | zero => simp [latticeInterval, hzero]
  | succ n ih =>
    have hsplit : latticeInterval (n + 1) =
        insert (-(n + 1 : ℤ)) (insert (n + 1 : ℤ) (latticeInterval n)) := by
      ext k
      simp only [latticeInterval, Nat.cast_add, Nat.cast_one, mem_Icc, mem_insert]
      omega
    have hpos : (n + 1 : ℤ) ∉ latticeInterval n := by
      simp [latticeInterval]
    have hneg : (-(n + 1 : ℤ)) ∉ insert (n + 1 : ℤ) (latticeInterval n) := by
      simp only [latticeInterval, mem_insert, mem_Icc]
      omega
    rw [hsplit, sum_insert hneg, sum_insert hpos, heven, ih, sum_range_succ _ (n + 1)]
    push_cast
    ring

private theorem card_latticeInterval (n : ℕ) :
    ((latticeInterval n).card : ℝ) = 2 * (n : ℝ) + 1 := by
  have h := Int.card_Icc_of_le (a := -(n : ℤ)) (b := (n : ℤ)) (by omega)
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h'
  unfold latticeInterval
  linarith [h']

private theorem sum_square_rat (n : ℕ) :
    (∑ j ∈ range (n + 1), (j : ℚ) ^ 2) =
      (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
  rw [sum_range_pow]
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two]
  ring

private theorem sum_fourth_rat (n : ℕ) :
    (∑ j ∈ range (n + 1), (j : ℚ) ^ 4) =
      (n : ℚ) * (n + 1) * (2 * n + 1) * (3 * (n : ℚ) ^ 2 + 3 * n - 1) / 30 := by
  have h3 : bernoulli 3 = 0 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_three]
  have h4 : bernoulli 4 = -(1 / 30 : ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
    norm_num
  have hc : (5 : ℕ).choose 2 = 10 := by decide
  rw [sum_range_pow]
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two, h3, h4, hc]
  ring

private theorem sum_lattice_square (n : ℕ) :
    (∑ k ∈ latticeInterval n, (k : ℝ) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 3 := by
  rw [sum_latticeInterval_even n _ (by simp) (by intro k; push_cast; ring)]
  push_cast
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_square_rat n)
  push_cast at h
  rw [h]
  ring

private theorem sum_lattice_fourth (n : ℕ) :
    (∑ k ∈ latticeInterval n, (k : ℝ) ^ 4) =
      (n : ℝ) * (n + 1) * (2 * n + 1) * (3 * (n : ℝ) ^ 2 + 3 * n - 1) / 15 := by
  rw [sum_latticeInterval_even n _ (by simp) (by intro k; push_cast; ring)]
  push_cast
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_fourth_rat n)
  push_cast at h
  rw [h]
  ring

private def normalizer (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ latticeInterval n, (t - (k : ℝ) ^ 2)

private def momentNumerator (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ latticeInterval n, (k : ℝ) ^ 2 * (t - (k : ℝ) ^ 2)

private theorem normalizer_formula (n : ℕ) (t : ℝ) :
    normalizer n t = (2 * (n : ℝ) + 1) * t - (n : ℝ) * (n + 1) * (2 * n + 1) / 3 := by
  rw [normalizer, sum_sub_distrib, sum_const, nsmul_eq_mul, card_latticeInterval,
    sum_lattice_square]

private theorem momentNumerator_formula (n : ℕ) (t : ℝ) :
    momentNumerator n t =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 3 * t -
      (n : ℝ) * (n + 1) * (2 * n + 1) * (3 * (n : ℝ) ^ 2 + 3 * n - 1) / 15 := by
  unfold momentNumerator
  simp_rw [mul_sub, ← pow_add]
  rw [sum_sub_distrib, ← sum_mul, sum_lattice_square, sum_lattice_fourth]
  ring

private theorem lower_moment_difference (n : ℕ) (t : ℝ) :
    momentNumerator n t - (((n : ℝ) ^ 2 - 1) / 5) * normalizer n t =
      (2 * (n : ℝ) + 1) * (n + 1) * (2 * n + 3) / 15 * (t - (n : ℝ) ^ 2) := by
  rw [normalizer_formula, momentNumerator_formula]
  ring

private theorem upper_moment_difference (n : ℕ) (t : ℝ) :
    momentNumerator n t - ((n : ℝ) * (n + 2) / 5) * normalizer n t =
      (2 * (n : ℝ) + 1) * n * (2 * (n : ℝ) - 1) / 15 * (t - ((n : ℝ) + 1) ^ 2) := by
  rw [normalizer_formula, momentNumerator_formula]
  ring

end D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
