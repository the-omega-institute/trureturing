/- GID: D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The largest real root of Dukes's cubic dominates both remaining eigenvalues. -/

import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! The cubic and the two explicit eigenvalues of the 1D 3-permaspin transfer matrix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder

open Polynomial

/-- Dukes's cubic, with its source coefficients at every real parameter pair. -/
noncomputable def dukesCubic (c d : ℝ) : Polynomial ℝ :=
  C 1 * X ^ 3 + C (-(c * d ^ 2 + c ^ 2 + 2 * c * d + c + 1)) * X ^ 2 +
    C (-(c * (c * d ^ 3 + 3 * c ^ 2 * d + c * d ^ 2 + c ^ 2 + c * d + c +
      3 * d + 1) * (d - 1))) * X +
    C ((d ^ 2 + 4 * d + 1) * c ^ 3 * (d + 1) * (d - 1) ^ 3)

/-- The supremum of all real roots of the source cubic. -/
noncomputable def largestRoot (c d : ℝ) : ℝ :=
  sSup {x : ℝ | (dukesCubic c d).eval x = 0}

/-- The root set exists and is bounded above, and its supremum dominates the two eigenvalues. -/
def claim : Prop :=
  ∀ c d : ℝ, 0 < c → 0 < d →
    {x : ℝ | (dukesCubic c d).eval x = 0}.Nonempty ∧
    BddAbove {x : ℝ | (dukesCubic c d).eval x = 0} ∧
    max (max (largestRoot c d) (c * (1 - d) ^ 2)) (c * (1 - d ^ 2)) = largestRoot c d

private theorem cubic_data (c d : ℝ) :
    (dukesCubic c d).degree = 3 ∧ (dukesCubic c d).leadingCoeff = 1 := by
  exact ⟨degree_cubic (by norm_num), leadingCoeff_cubic (by norm_num)⟩

private theorem cubic_at_comparison (c d : ℝ) :
    (dukesCubic c d).eval (c * (1 + d) ^ 2) =
      -4 * c ^ 2 * d ^ 2 * (d + 1) * ((d + 1) * (c - 1) ^ 2 + 4 * c * d) := by
  rw [dukesCubic.eq_1]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

private theorem cubic_at_comparison_neg (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    (dukesCubic c d).eval (c * (1 + d) ^ 2) < 0 := by
  rw [cubic_at_comparison]
  have hinner : 0 < (d + 1) * (c - 1) ^ 2 + 4 * c * d := by positivity
  have hpos : 0 < 4 * c ^ 2 * d ^ 2 * (d + 1) *
      ((d + 1) * (c - 1) ^ 2 + 4 * c * d) := by positivity
  nlinarith only [hpos]

private theorem roots_bddAbove (c d : ℝ) :
    BddAbove {x : ℝ | (dukesCubic c d).eval x = 0} := by
  have hdeg : 0 < (dukesCubic c d).degree := by rw [(cubic_data c d).1]; norm_num
  exact (dukesCubic c d).exists_max_root (ne_zero_of_degree_gt hdeg)

private theorem root_above_comparison (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    ∃ r : ℝ, c * (1 + d) ^ 2 < r ∧ (dukesCubic c d).eval r = 0 := by
  have hdeg : 0 < (dukesCubic c d).degree := by rw [(cubic_data c d).1]; norm_num
  have hlc : 0 ≤ (dukesCubic c d).leadingCoeff := by rw [(cubic_data c d).2]; norm_num
  exact intermediate_value_Ioi (dukesCubic c d).continuous.continuousOn
    ((dukesCubic c d).tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc)
    (cubic_at_comparison_neg c d hc hd)

private theorem comparison_gaps (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    c * (1 - d) ^ 2 < c * (1 + d) ^ 2 ∧
    c * (1 - d ^ 2) < c * (1 + d) ^ 2 := by
  constructor
  · nlinarith only [mul_pos hc hd]
  · have hgap : 0 < c * d * (d + 1) := by positivity
    nlinarith only [hgap]

/-- The largest root is the largest of the three candidate transfer-matrix eigenvalues. -/
theorem result : claim := by
  intro c d hc hd
  obtain ⟨r, hqr, hr⟩ := root_above_comparison c d hc hd
  have hb := roots_bddAbove c d
  have hrle : r ≤ largestRoot c d := le_csSup hb hr
  obtain ⟨hfour, hfive⟩ := comparison_gaps c d hc hd
  refine ⟨⟨r, hr⟩, hb, ?_⟩
  rw [max_eq_left (hfour.le.trans (hqr.le.trans hrle)),
    max_eq_left (hfive.le.trans (hqr.le.trans hrle))]

end D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder
