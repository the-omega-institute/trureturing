/- GID: D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact defect and optimal fit of cyclic equal-rim unit-quaternion gains. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The cyclic rim on four vertices has an exact minimax radius at every angle.
The ratio of this radius to the triangle defect is maximal at the quarter turn. -/

noncomputable section

open Real

namespace RoundQuaternionEqualRimMinimax

/-- The maximum principal angle of a spoke triangle and the cyclic rim triangle. -/
def equalRimDefect (a : ℝ) : ℝ :=
  if a ≤ π / 3 then 3 * a else if a ≤ π / 2 then 2 * π - 3 * a else a

private def rimEigenvalue (a : ℝ) : ℝ := cos (a - 2 * π / 3)

private def optimalScore (a : ℝ) : ℝ :=
  let l := rimEigenvalue a
  let d := l - cos a
  if 0 < d then (-1 + √(1 + 4 * l * d)) / (2 * d) else l

/-- The sharp radius as a function of the common rim angle. -/
def equalRimOptRadius (a : ℝ) : ℝ :=
  if a ≤ π / 3 then a else arccos (optimalScore a)

private theorem defect_eq_max (a : ℝ) (ha : a ∈ Set.Icc 0 π) :
    equalRimDefect a = max a (arccos (cos (3 * a))) := by
  by_cases h₁ : a ≤ π / 3
  · rw [equalRimDefect, if_pos h₁, arccos_cos (by linarith [ha.1]) (by linarith),
      max_eq_right (by linarith [ha.1])]
  rw [equalRimDefect, if_neg h₁]
  by_cases h₂ : a ≤ π / 2
  · rw [if_pos h₂, ← cos_two_pi_sub, arccos_cos (by linarith [pi_pos])
      (by linarith), max_eq_right (by linarith)]
  rw [if_neg h₂]
  apply (max_eq_left _).symm
  rcases le_or_gt a (2 * π / 3) with h₃ | h₃
  · rw [← cos_two_pi_sub, arccos_cos (by linarith) (by linarith [pi_pos])]
    linarith
  · rw [show cos (3 * a) = cos (3 * a - 2 * π) by
        rw [← cos_add_two_pi (3 * a - 2 * π)]
        congr 1 <;> ring,
      arccos_cos (by linarith) (by linarith [ha.2])]
    linarith [ha.2]

private theorem rim_eigenvalue_formula (a : ℝ) :
    rimEigenvalue a = -cos a / 2 + √3 / 2 * sin a := by
  have hc : cos (2 * π / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have hs : sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]
  rw [rimEigenvalue, cos_sub, hc, hs]
  ring

private theorem eigenvalue_gap (a : ℝ) :
    rimEigenvalue a - cos a = √3 * sin (a - π / 3) := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  rw [rim_eigenvalue_formula, sin_sub, cos_pi_div_three, sin_pi_div_three]
  nlinarith

private theorem eigenvalue_le_cos {a : ℝ} (ha : 0 ≤ a) (h : a ≤ π / 3) :
    rimEigenvalue a ≤ cos a := by
  have hs : 0 ≤ sin (π / 3 - a) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  rw [show π / 3 - a = -(a - π / 3) by ring, sin_neg] at hs
  linarith [eigenvalue_gap a, mul_nonpos_of_nonneg_of_nonpos
    (sqrt_nonneg 3) (show sin (a - π / 3) ≤ 0 by linarith)]

private theorem cos_lt_eigenvalue {a : ℝ} (h : π / 3 < a) (ha : a ≤ π) :
    cos a < rimEigenvalue a := by
  have hs : 0 < sin (a - π / 3) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  linarith [eigenvalue_gap a, mul_pos (sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)) hs]

private theorem eigenvalue_pos {a : ℝ} (h : π / 3 ≤ a) (ha : a ≤ π) :
    0 < rimEigenvalue a := by
  have hx : |a - 2 * π / 3| ≤ π / 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have hc := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (a - 2 * π / 3))
    (show π / 3 ≤ π by linarith [pi_pos]) hx
  rw [cos_abs, cos_pi_div_three] at hc
  unfold rimEigenvalue
  linarith

private theorem optimal_score_spec {a : ℝ} (h : π / 3 < a) (ha : a ≤ π) :
    0 < optimalScore a ∧ optimalScore a ≤ 1 ∧
      (rimEigenvalue a - cos a) * optimalScore a ^ 2 + optimalScore a = rimEigenvalue a := by
  let l := rimEigenvalue a
  let d := l - cos a
  let s := √(1 + 4 * l * d)
  have hd : 0 < d := sub_pos.2 (cos_lt_eigenvalue h ha)
  have hl : 0 < l := eigenvalue_pos h.le ha
  have hld := mul_pos hl hd
  have hsq : s ^ 2 = 1 + 4 * l * d := sq_sqrt (by linarith)
  have hs : 1 < s := by
    by_contra! hs
    have hs₀ : 0 ≤ s := sqrt_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.2 hs) (show 0 ≤ s + 1 by linarith)]
  have ht : optimalScore a = (s - 1) / (2 * d) := by
    unfold optimalScore
    dsimp only
    rw [if_pos hd]
    congr 1 <;> ring
  have htpos : 0 < optimalScore a := by rw [ht]; positivity
  have hroot : d * optimalScore a ^ 2 + optimalScore a = l := by
    rw [ht]
    field_simp [ne_of_gt hd]
    nlinarith
  refine ⟨htpos, ?_, hroot⟩
  by_contra! ht
  have hsq₁ : 1 ≤ optimalScore a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht.le) (show 0 ≤ optimalScore a + 1 by linarith)]
  have hlow := mul_le_mul_of_nonneg_left hsq₁ hd.le
  have hc : cos a ≤ 1 := cos_le_one a
  dsimp [d] at hlow hroot
  linarith

private theorem score_le_optimal {a u : ℝ} (h : π / 3 < a) (ha : a ≤ π)
    (hu : u ≤ rimEigenvalue a - (rimEigenvalue a - cos a) * u ^ 2) :
    u ≤ optimalScore a := by
  obtain ⟨ht, _, hroot⟩ := optimal_score_spec h ha
  by_contra! hlt
  have hsq : optimalScore a ^ 2 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (show 0 ≤ u + optimalScore a by linarith)]
  have hd := sub_pos.2 (cos_lt_eigenvalue h ha)
  linarith [mul_le_mul_of_nonneg_left hsq hd.le]

private theorem score_unique {a u : ℝ} (h : π / 3 < a) (ha : a ≤ π) (hu : 0 < u)
    (he : (rimEigenvalue a - cos a) * u ^ 2 + u = rimEigenvalue a) :
    u = optimalScore a := by
  apply le_antisymm (score_le_optimal h ha (by linarith))
  obtain ⟨_, _, hroot⟩ := optimal_score_spec h ha
  by_contra! hlt
  have hsq : u ^ 2 ≤ optimalScore a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (show 0 ≤ u + optimalScore a by linarith)]
  have hd := sub_pos.2 (cos_lt_eigenvalue h ha)
  linarith [mul_le_mul_of_nonneg_left hsq hd.le]

private theorem arccos_cos_mul_convex {q : ℝ} (hq : 0 ≤ q) (hq₁ : q < 1) :
    ConvexOn ℝ (Set.Icc 0 (π / 2)) (fun s => arccos (q * cos s)) := by
  let d : ℝ → ℝ := fun s => 1 - (q * cos s) ^ 2
  let f : ℝ → ℝ := fun s => arccos (q * cos s)
  let f' : ℝ → ℝ := fun s => q * sin s / √(d s)
  have hbound (s : ℝ) : |q * cos s| < 1 := by
    rw [abs_mul, abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left (abs_cos_le_one s) hq).trans_lt (by simpa using hq₁)
  have hpos (s : ℝ) : 0 < d s := by
    have hh := abs_lt.1 (hbound s)
    dsimp [d]
    nlinarith [mul_pos (sub_pos.2 hh.2) (show 0 < 1 + q * cos s by linarith)]
  have hf (s : ℝ) : HasDerivAt f (f' s) s := by
    have hh := abs_lt.1 (hbound s)
    have hh' := (hasDerivAt_cos s).const_mul q
    convert (hasDerivAt_arccos (ne_of_gt hh.1) (ne_of_lt hh.2)).comp s hh' using 1
    dsimp [f', d]
    ring
  have hf' (s : ℝ) :
      HasDerivAt f' (q * (1 - q ^ 2) * cos s / (√(d s)) ^ 3) s := by
    have hcos := (hasDerivAt_cos s).const_mul q
    have hs := ((hcos.pow 2).const_sub 1).sqrt (ne_of_gt (hpos s))
    have hr := ((hasDerivAt_sin s).const_mul q).div hs (ne_of_gt (sqrt_pos.2 (hpos s)))
    convert hr using 1
    have hss : (√(d s)) ^ 2 = d s := sq_sqrt (hpos s).le
    have hsn := sin_sq_add_cos_sq s
    change q * (1 - q ^ 2) * cos s / (√(d s)) ^ 3 =
      (q * cos s * √(d s) -
        q * sin s * ((-(2 * (q * cos s) ^ (2 - 1) * (q * -sin s))) / (2 * √(d s)))) /
        (√(d s)) ^ 2
    field_simp [ne_of_gt (sqrt_pos.2 (hpos s))]
    linear_combination
      q * cos s * (√(d s)) ^ 2 * (hss.trans (show d s = 1 - (q * cos s) ^ 2 from rfl)).symm +
      q ^ 3 * cos s * (√(d s)) ^ 2 * hsn.symm
  have hderiv : deriv f = f' := funext (fun s => (hf s).deriv)
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 _) (by
      exact (continuous_arccos.comp (continuous_const.mul continuous_cos)).continuousOn)
    (fun s _ => (hf s).differentiableAt.differentiableWithinAt) ?_ ?_
  · rw [hderiv]
    exact fun s _ => (hf' s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [Function.iterate_succ_apply', Function.iterate_one, hderiv, (hf' s).deriv]
    have hs' := interior_subset hs
    have hcos : 0 ≤ cos s := cos_nonneg_of_mem_Icc
      ⟨by linarith [hs'.1, pi_pos], hs'.2⟩
    have hq₂ : 0 ≤ 1 - q ^ 2 := by nlinarith [mul_nonneg hq hq₁.le]
    positivity

end RoundQuaternionEqualRimMinimax
