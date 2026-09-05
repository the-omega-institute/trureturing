/- GID: D5/S3/Analytic/Boundary/ActiveSemicircle
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/ActiveSemicircle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A reflected rational response is negative exactly inside its active semicircle. -/

import Mathlib.Tactic

/-!
# Active semicircle

A reflected off-line pair contributes the sum of two real rational terms
below.  Away from its pole, a common-denominator calculation factors the sign
through `x^2 + (t - gamma)^2 - delta^2`.  In the right half-plane this gives
the exact open semicircle on which the response is negative.

The source statement is corrected here by making its analytic domain explicit:
`delta` and `x` are positive, and the denominator belonging to the right-half-
plane pole is nonzero.  This last premise is essential for the intended
rational function even though Lean totalizes division by zero as zero.

Library-search and duplication audit (2026-09-03):

* Keyword searches for active semicircles, half-disks, and reflected rational
  responses, together with symbol-shape searches for the two denominators,
  found no theorem owner under `D5/`.
* The formalization receipt index is retired in the current repository regime;
  the digestion ledger contains only this atom's residual-open entry before
  coverage, and no accepted edge for it.
* Digest-index and generalized sign-factorization searches found nearby
  curvature dipoles but no theorem for this first-order two-pole response.
* Every remote `origin/lane/math/*` branch was searched and contains no
  in-flight implementation of this atom or an equivalent theorem.
* Pinned Mathlib supplies ordered-field quotient lemmas, `exists_nat_gt`,
  `field_simp`, and `ring`; they are applied directly below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Boundary.ActiveSemicircle

/-- The real response of a reflected pair at horizontal coordinate `x` and
tangential coordinate `t`. -/
def activeSemicircleResponse (delta gamma x t : ℝ) : ℝ :=
  (x - delta) / ((x - delta) ^ 2 + (t - gamma) ^ 2) +
    (x + delta) / ((x + delta) ^ 2 + (t - gamma) ^ 2)

private theorem response_factorization
    (delta gamma x t : ℝ)
    (hMinus : (x - delta) ^ 2 + (t - gamma) ^ 2 ≠ 0)
    (hPlus : (x + delta) ^ 2 + (t - gamma) ^ 2 ≠ 0) :
    activeSemicircleResponse delta gamma x t =
      2 * x * (x ^ 2 + (t - gamma) ^ 2 - delta ^ 2) /
        (((x - delta) ^ 2 + (t - gamma) ^ 2) *
          ((x + delta) ^ 2 + (t - gamma) ^ 2)) := by
  unfold activeSemicircleResponse
  field_simp [hMinus, hPlus]
  ring

/-- In the right half-plane and away from the pole, the reflected response is
strictly negative exactly inside the open semicircle of radius `delta` centered
at the boundary point `(0, gamma)`. -/
theorem active_semicircle_criterion
    (delta gamma x t : ℝ) (hdelta : 0 < delta) (hx : 0 < x)
    (hPole : (x - delta) ^ 2 + (t - gamma) ^ 2 ≠ 0) :
    activeSemicircleResponse delta gamma x t < 0 ↔
      x ^ 2 + (t - gamma) ^ 2 < delta ^ 2 := by
  have hMinusNonneg :
      0 ≤ (x - delta) ^ 2 + (t - gamma) ^ 2 := by positivity
  have hMinusPos :
      0 < (x - delta) ^ 2 + (t - gamma) ^ 2 :=
    lt_of_le_of_ne hMinusNonneg hPole.symm
  have hPlusPos :
      0 < (x + delta) ^ 2 + (t - gamma) ^ 2 := by
    nlinarith [sq_pos_of_pos (add_pos hx hdelta), sq_nonneg (t - gamma)]
  have hDenominatorPos :
      0 < ((x - delta) ^ 2 + (t - gamma) ^ 2) *
        ((x + delta) ^ 2 + (t - gamma) ^ 2) :=
    mul_pos hMinusPos hPlusPos
  have hScalePos : 0 < 2 * x := mul_pos (by norm_num) hx
  rw [response_factorization delta gamma x t hPole hPlusPos.ne']
  constructor
  · intro hNegative
    have hNumeratorNegative :
        2 * x * (x ^ 2 + (t - gamma) ^ 2 - delta ^ 2) < 0 := by
      have := (div_lt_iff₀ hDenominatorPos).1 hNegative
      simpa only [zero_mul] using this
    rcases (mul_neg_iff.mp hNumeratorNegative) with hSign | hSign
    · exact sub_neg.mp hSign.2
    · exact False.elim ((not_lt_of_ge hScalePos.le) hSign.1)
  · intro hInside
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg hScalePos (sub_neg.mpr hInside))
      hDenominatorPos

/-- Every non-pole point of the bounding semicircle has zero response.  This
is the equality witness separating the negative interior from the exterior. -/
theorem active_semicircle_boundary_zero
    (delta gamma x t : ℝ) (hdelta : 0 < delta) (hx : 0 < x)
    (hPole : (x - delta) ^ 2 + (t - gamma) ^ 2 ≠ 0)
    (hBoundary : x ^ 2 + (t - gamma) ^ 2 = delta ^ 2) :
    activeSemicircleResponse delta gamma x t = 0 := by
  have hPlusPos :
      0 < (x + delta) ^ 2 + (t - gamma) ^ 2 := by
    nlinarith [sq_pos_of_pos (add_pos hx hdelta), sq_nonneg (t - gamma)]
  rw [response_factorization delta gamma x t hPole hPlusPos.ne']
  simp [hBoundary]

/-- The bounding circle meets the critical axis at `gamma - delta` and
`gamma + delta`; both endpoints attain zero response. -/
theorem active_semicircle_axis_endpoints
    (delta gamma : ℝ) (hdelta : 0 < delta) :
    (0 ^ 2 + ((gamma - delta) - gamma) ^ 2 = delta ^ 2 ∧
      activeSemicircleResponse delta gamma 0 (gamma - delta) = 0) ∧
    (0 ^ 2 + ((gamma + delta) - gamma) ^ 2 = delta ^ 2 ∧
      activeSemicircleResponse delta gamma 0 (gamma + delta) = 0) := by
  have hLeftMinus :
      ((0 : ℝ) - delta) ^ 2 + ((gamma - delta) - gamma) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hdelta]
  have hLeftPlus :
      ((0 : ℝ) + delta) ^ 2 + ((gamma - delta) - gamma) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hdelta]
  have hRightMinus :
      ((0 : ℝ) - delta) ^ 2 + ((gamma + delta) - gamma) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hdelta]
  have hRightPlus :
      ((0 : ℝ) + delta) ^ 2 + ((gamma + delta) - gamma) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hdelta]
  constructor
  · constructor
    · ring
    · rw [response_factorization delta gamma 0 (gamma - delta)
        hLeftMinus hLeftPlus]
      simp
  · constructor
    · ring
    · rw [response_factorization delta gamma 0 (gamma + delta)
        hRightMinus hRightPlus]
      simp

private theorem left_pole_sequence_formula
    (delta gamma : ℝ) (hdelta : 0 < delta) (n : ℕ) :
    activeSemicircleResponse delta gamma
        (delta - delta / ((n : ℝ) + 2)) gamma =
      (-((n : ℝ) + 2) +
        ((n : ℝ) + 2) / (2 * (n : ℝ) + 3)) / delta := by
  have hnTwo : (n : ℝ) + 2 ≠ 0 := by positivity
  have hnThree : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hStepPos : 0 < delta / ((n : ℝ) + 2) := by positivity
  have hStepLt : delta / ((n : ℝ) + 2) < delta := by
    rw [div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)]
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hMinus :
      ((delta - delta / ((n : ℝ) + 2)) - delta) ^ 2 +
          (gamma - gamma) ^ 2 ≠ 0 := by
    have hDifference :
        (delta - delta / ((n : ℝ) + 2)) - delta ≠ 0 := by
      nlinarith
    nlinarith [sq_pos_of_ne_zero hDifference]
  have hPlus :
      ((delta - delta / ((n : ℝ) + 2)) + delta) ^ 2 +
          (gamma - gamma) ^ 2 ≠ 0 := by
    have hDifference :
        0 < (delta - delta / ((n : ℝ) + 2)) + delta := by
      nlinarith
    nlinarith [sq_pos_of_pos hDifference]
  have hFirst :
      ((delta - delta / ((n : ℝ) + 2)) - delta) /
          (((delta - delta / ((n : ℝ) + 2)) - delta) ^ 2 +
            (gamma - gamma) ^ 2) =
        -((n : ℝ) + 2) / delta := by
    apply (div_eq_iff hMinus).2
    field_simp [hdelta.ne', hnTwo]
    ring
  have hSecond :
      ((delta - delta / ((n : ℝ) + 2)) + delta) /
          (((delta - delta / ((n : ℝ) + 2)) + delta) ^ 2 +
            (gamma - gamma) ^ 2) =
        ((n : ℝ) + 2) / (delta * (2 * (n : ℝ) + 3)) := by
    apply (div_eq_iff hPlus).2
    field_simp [hdelta.ne', hnTwo, hnThree]
    ring
  unfold activeSemicircleResponse
  rw [hFirst, hSecond]
  field_simp [hdelta.ne', hnThree]

private theorem left_pole_sequence_bound
    (delta gamma : ℝ) (hdelta : 0 < delta) (n : ℕ) :
    activeSemicircleResponse delta gamma
        (delta - delta / ((n : ℝ) + 2)) gamma ≤
      (-((n : ℝ) + 1)) / delta := by
  rw [left_pole_sequence_formula delta gamma hdelta n]
  rw [div_le_div_iff_of_pos_right hdelta]
  have hDenominator : 0 < 2 * (n : ℝ) + 3 := by positivity
  have hFraction :
      ((n : ℝ) + 2) / (2 * (n : ℝ) + 3) ≤ 1 := by
    exact (div_le_one hDenominator).2 (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  linarith

/-- Along the horizontal line through the pole, points can be chosen strictly
to its left in the right half-plane with response below any prescribed real
bound. -/
theorem active_semicircle_response_unbounded_near_pole
    (delta gamma : ℝ) (hdelta : 0 < delta) (bound : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x < delta ∧
      activeSemicircleResponse delta gamma x gamma < bound := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (-bound * delta)
  let x := delta - delta / ((n : ℝ) + 2)
  have hDenominator : 0 < (n : ℝ) + 2 := by positivity
  have hStepPos : 0 < delta / ((n : ℝ) + 2) :=
    div_pos hdelta hDenominator
  have hStepLt : delta / ((n : ℝ) + 2) < delta := by
    rw [div_lt_iff₀ hDenominator]
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  refine ⟨x, by dsimp only [x]; linarith, by dsimp only [x]; linarith, ?_⟩
  calc
    activeSemicircleResponse delta gamma x gamma ≤
        (-((n : ℝ) + 1)) / delta := by
      simpa only [x] using left_pole_sequence_bound delta gamma hdelta n
    _ < bound := by
      rw [div_lt_iff₀ hdelta]
      nlinarith [hn]

/-- Adding any background that is bounded above between the axis and the pole
still yields a negative total response sufficiently near the pole. -/
theorem active_semicircle_bounded_background_loses_nonnegativity
    (delta gamma : ℝ) (hdelta : 0 < delta)
    (background : ℝ → ℝ) (bound : ℝ)
    (hBackground : ∀ x, 0 < x → x < delta → background x ≤ bound) :
    ∃ x : ℝ, 0 < x ∧ x < delta ∧
      activeSemicircleResponse delta gamma x gamma + background x < 0 := by
  obtain ⟨x, hx, hxdelta, hResponse⟩ :=
    active_semicircle_response_unbounded_near_pole
      delta gamma hdelta (-bound)
  refine ⟨x, hx, hxdelta, ?_⟩
  nlinarith [hBackground x hx hxdelta]

#print axioms active_semicircle_criterion
#print axioms active_semicircle_boundary_zero
#print axioms active_semicircle_axis_endpoints
#print axioms active_semicircle_response_unbounded_near_pole
#print axioms active_semicircle_bounded_background_loses_nonnegativity

end D5.S3.Analytic.Boundary.ActiveSemicircle
