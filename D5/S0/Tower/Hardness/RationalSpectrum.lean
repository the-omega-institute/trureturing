/- GID: D5/S0/Tower/Hardness/RationalSpectrum
   generality: E
   mirror-B: D5/B/S0/Tower/Hardness/RationalSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Package hardness definitions with the sharp rational-tower Hurwitz extremum. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/- Library-search audit trail (2026-08-17):
   * Pinned Mathlib v4.31.0 was searched for Hurwitz, Lagrange-Markov,
     badly approximable, rational approximation, continued fractions,
     sqrt five, and the golden ratio.  Dirichlet's constant-one theorem
     (`Real.exists_rat_abs_sub_le_and_den_le`), its infinite irrational
     consequence, and Legendre's constant-one-half convergent criterion were
     found, but no sharp Hurwitz constant-one-over-sqrt-five theorem was found.
   * Loogle searches for `Hurwitz`, `badly approximable`, and the exact
     Dirichlet declaration found no sharp Diophantine Hurwitz result.
   * LeanSearch queries for the sharp irrational-approximation theorem and
     golden-ratio extremality returned Dirichlet, Legendre, irrationality, and
     Liouville results, but no exact hit.  GitHub Lean code searches for
     Hurwitz, sqrt-five rational approximation, and badly approximable also
     returned no exact hit.
   * The declaration below therefore proves the missing sharp three-convergent
     inequality over normalized regular-continued-fraction coordinates.
-/

namespace D5.S0.Tower.Hardness.RationalSpectrum

open Filter

noncomputable section

/-- A normalized nonterminating regular-continued-fraction orbit.  The
`backwardTail` recurrence is the denominator-ratio recurrence, while the
`forwardTail` recurrence is the complete-quotient recurrence. -/
structure RationalTowerPoint where
  partialQuotient : Nat -> Nat
  backwardTail : Nat -> Real
  forwardTail : Nat -> Real
  partialQuotient_pos : forall n, 0 < partialQuotient n
  backwardTail_nonneg : forall n, 0 <= backwardTail n
  backwardTail_pos_succ : forall n, 0 < backwardTail (n + 1)
  forwardTail_pos : forall n, 0 < forwardTail n
  backward_recurrence : forall n,
    backwardTail (n + 1) = 1 / ((partialQuotient n : Real) + backwardTail n)
  forward_recurrence : forall n,
    forwardTail n = 1 / ((partialQuotient (n + 1) : Real) + forwardTail (n + 1))

/-- The normalized convergent error `q_n^2 * |x - p_n / q_n|` in forward/backward-tail
coordinates. -/
def approximationCoefficient (point : RationalTowerPoint) (n : Nat) : Real :=
  1 / ((point.partialQuotient n : Real) + point.backwardTail n + point.forwardTail n)

/-- The hardness of a rational-tower point is the lower limit of its normalized
convergent errors. -/
def rationalHardness (point : RationalTowerPoint) : Real :=
  liminf (approximationCoefficient point) atTop

/-- The hardness spectrum attached to a hardness function. -/
def hardnessSpectrum {X : Type} (beta : X -> Real) : Set Real := Set.range beta

/-- A point is badly approximable exactly when its hardness is positive. -/
def BadlyApproximable {X : Type} (beta : X -> Real) (x : X) : Prop := 0 < beta x

theorem partial_quotient_one_le (point : RationalTowerPoint) (n : Nat) :
    (1 : Real) <= point.partialQuotient n := by
  exact_mod_cast point.partialQuotient_pos n

theorem approximation_coefficient_pos (point : RationalTowerPoint) (n : Nat) :
    0 < approximationCoefficient point n := by
  rw [approximationCoefficient]
  apply one_div_pos.mpr
  nlinarith [partial_quotient_one_le point n, point.backwardTail_nonneg n,
    point.forwardTail_pos n]

/-- The sharp algebraic core of Hurwitz's theorem: among the center coefficient
and its two normalized neighbors, at least one is at most `1 / sqrt 5`. -/
theorem hurwitz_triple_algebra
    (a r y : Real) (ha : 1 <= a) (hr : 0 < r) (hy : 0 < y) :
    1 / (a + r + y) <= 1 / Real.sqrt 5 \/
      r * (a + y) / (a + r + y) <= 1 / Real.sqrt 5 \/
      y * (a + r) / (a + r + y) <= 1 / Real.sqrt 5 := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hden : 0 < a + r + y := by linarith
  by_contra h
  simp only [not_or, not_le] at h
  rcases h with ⟨hcenter, hprevious, hnext⟩
  have hden_lt : a + r + y < Real.sqrt 5 :=
    (one_div_lt_one_div hs hden).mp hcenter
  rcases le_total r y with hry | hyr
  · have hbalanced : 0 <= (y - r) * (2 * a + y - r) :=
      mul_nonneg (sub_nonneg.mpr hry) (by linarith)
    have ha_sq : 0 <= (a - 1) * (a + 1) :=
      mul_nonneg (sub_nonneg.mpr ha) (by linarith)
    have hradical :
        0 <= (Real.sqrt 5 - (a + r + y)) *
          (Real.sqrt 5 * (a + r + y) + 1) :=
      mul_nonneg (sub_nonneg.mpr hden_lt.le) (by positivity)
    have hsmall : Real.sqrt 5 * (r * (a + y)) <= a + r + y := by
      nlinarith
    have hle : r * (a + y) / (a + r + y) <= 1 / Real.sqrt 5 := by
      apply (div_le_div_iff₀ hden hs).2
      nlinarith
    exact (not_lt_of_ge hle) hprevious
  · have hbalanced : 0 <= (r - y) * (2 * a + r - y) :=
      mul_nonneg (sub_nonneg.mpr hyr) (by linarith)
    have ha_sq : 0 <= (a - 1) * (a + 1) :=
      mul_nonneg (sub_nonneg.mpr ha) (by linarith)
    have hradical :
        0 <= (Real.sqrt 5 - (a + r + y)) *
          (Real.sqrt 5 * (a + r + y) + 1) :=
      mul_nonneg (sub_nonneg.mpr hden_lt.le) (by positivity)
    have hsmall : Real.sqrt 5 * (y * (a + r)) <= a + r + y := by
      nlinarith
    have hle : y * (a + r) / (a + r + y) <= 1 / Real.sqrt 5 := by
      apply (div_le_div_iff₀ hden hs).2
      nlinarith
    exact (not_lt_of_ge hle) hnext

theorem reciprocal_sum_identity (u v : Real) (hu : 0 < u) (hv : 0 < v) :
    1 / (u + 1 / v) = (1 / u) * v / (v + 1 / u) := by
  have huv : 0 < u * v + 1 := by positivity
  field_simp [hu.ne', hv.ne', huv.ne']

theorem approximation_coefficient_previous (point : RationalTowerPoint) (n : Nat) :
    approximationCoefficient point n =
      point.backwardTail (n + 1) *
        ((point.partialQuotient (n + 1) : Real) + point.forwardTail (n + 1)) /
          ((point.partialQuotient (n + 1) : Real) + point.backwardTail (n + 1) +
            point.forwardTail (n + 1)) := by
  rw [approximationCoefficient, point.backward_recurrence n, point.forward_recurrence n]
  have hleft : 0 < (point.partialQuotient n : Real) + point.backwardTail n := by
    nlinarith [partial_quotient_one_le point n, point.backwardTail_nonneg n]
  have hright : 0 <
      (point.partialQuotient (n + 1) : Real) + point.forwardTail (n + 1) := by
    nlinarith [partial_quotient_one_le point (n + 1), point.forwardTail_pos (n + 1)]
  simpa [add_assoc, add_comm, add_left_comm] using reciprocal_sum_identity
    ((point.partialQuotient n : Real) + point.backwardTail n)
    ((point.partialQuotient (n + 1) : Real) + point.forwardTail (n + 1)) hleft hright

theorem approximation_coefficient_next (point : RationalTowerPoint) (n : Nat) :
    approximationCoefficient point (n + 2) =
      point.forwardTail (n + 1) *
        ((point.partialQuotient (n + 1) : Real) + point.backwardTail (n + 1)) /
          ((point.partialQuotient (n + 1) : Real) + point.backwardTail (n + 1) +
            point.forwardTail (n + 1)) := by
  rw [approximationCoefficient, point.backward_recurrence (n + 1),
    point.forward_recurrence (n + 1)]
  have hleft : 0 <
      (point.partialQuotient (n + 1) : Real) + point.backwardTail (n + 1) := by
    nlinarith [partial_quotient_one_le point (n + 1), point.backwardTail_pos_succ n]
  have hright : 0 <
      (point.partialQuotient (n + 2) : Real) + point.forwardTail (n + 2) := by
    nlinarith [partial_quotient_one_le point (n + 2), point.forwardTail_pos (n + 2)]
  simpa [add_assoc, add_comm, add_left_comm] using reciprocal_sum_identity
    ((point.partialQuotient (n + 2) : Real) + point.forwardTail (n + 2))
    ((point.partialQuotient (n + 1) : Real) + point.backwardTail (n + 1)) hright hleft

theorem approximation_coefficient_triple (point : RationalTowerPoint) (n : Nat) :
    approximationCoefficient point n <= 1 / Real.sqrt 5 \/
      approximationCoefficient point (n + 1) <= 1 / Real.sqrt 5 \/
      approximationCoefficient point (n + 2) <= 1 / Real.sqrt 5 := by
  have h := hurwitz_triple_algebra
    (point.partialQuotient (n + 1) : Real)
    (point.backwardTail (n + 1)) (point.forwardTail (n + 1))
    (partial_quotient_one_le point (n + 1))
    (point.backwardTail_pos_succ n) (point.forwardTail_pos (n + 1))
  rcases h with hcenter | hprevious | hnext
  · exact Or.inr (Or.inl (by simpa [approximationCoefficient] using hcenter))
  · exact Or.inl ((approximation_coefficient_previous point n).trans_le hprevious)
  · exact Or.inr (Or.inr ((approximation_coefficient_next point n).trans_le hnext))

theorem rational_hardness_le_hurwitz (point : RationalTowerPoint) :
    rationalHardness point <= 1 / Real.sqrt 5 := by
  apply Filter.liminf_le_of_frequently_le
  · rw [Filter.frequently_atTop]
    intro N
    rcases approximation_coefficient_triple point N with hN | hN | hN
    · exact ⟨N, le_rfl, hN⟩
    · exact ⟨N + 1, Nat.le_add_right N 1, hN⟩
    · exact ⟨N + 2, Nat.le_add_right N 2, hN⟩
  · apply Filter.isBoundedUnder_of_eventually_ge
    exact Eventually.of_forall fun n => (approximation_coefficient_pos point n).le

/-- The fixed normalized tail of the all-one continued fraction. -/
def goldenTail : Real := Real.goldenRatio⁻¹

theorem golden_tail_pos : 0 < goldenTail := by
  exact inv_pos.mpr Real.goldenRatio_pos

theorem golden_tail_quadratic : goldenTail ^ 2 + goldenTail = 1 := by
  rw [goldenTail, Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

theorem golden_tail_recurrence : goldenTail = 1 / (1 + goldenTail) := by
  have hpos : 0 < 1 + goldenTail := by linarith [golden_tail_pos]
  apply (eq_div_iff hpos.ne').2
  nlinarith [golden_tail_quadratic]

/-- The two-sided normalized rational-tower point with continued-fraction tail
`[1; 1, 1, ...]`, namely the golden-ratio equivalence class. -/
def goldenRatioPoint : RationalTowerPoint where
  partialQuotient := fun _ => 1
  backwardTail := fun _ => goldenTail
  forwardTail := fun _ => goldenTail
  partialQuotient_pos := by norm_num
  backwardTail_nonneg := fun _ => golden_tail_pos.le
  backwardTail_pos_succ := fun _ => golden_tail_pos
  forwardTail_pos := fun _ => golden_tail_pos
  backward_recurrence := fun _ => by simpa using golden_tail_recurrence
  forward_recurrence := fun _ => by simpa using golden_tail_recurrence

theorem golden_approximation_coefficient (n : Nat) :
    approximationCoefficient goldenRatioPoint n = 1 / Real.sqrt 5 := by
  have hsum : Real.goldenRatio + Real.goldenConj = 1 :=
    Real.goldenRatio_add_goldenConj
  have hdiff : Real.goldenRatio - Real.goldenConj = Real.sqrt 5 :=
    Real.goldenRatio_sub_goldenConj
  have htail : goldenTail = Real.goldenRatio - 1 := by
    rw [goldenTail, Real.inv_goldenRatio]
    linarith
  have hden : (1 : Real) + goldenTail + goldenTail = Real.sqrt 5 := by
    rw [htail]
    linarith [hsum, hdiff]
  simp only [approximationCoefficient, goldenRatioPoint]
  norm_num only [Nat.cast_one]
  rw [hden]

theorem golden_ratio_hardness :
    rationalHardness goldenRatioPoint = 1 / Real.sqrt 5 := by
  rw [rationalHardness]
  calc
    liminf (approximationCoefficient goldenRatioPoint) atTop =
        liminf (fun _ : Nat => 1 / Real.sqrt 5) atTop :=
      Filter.liminf_congr (Eventually.of_forall golden_approximation_coefficient)
    _ = 1 / Real.sqrt 5 := Filter.liminf_const (1 / Real.sqrt 5)

/-- Definition 4.1 as one coverable package.  Its third clause says that the set
of upper bounds of the rational hardness spectrum has least element `1 / sqrt 5`;
equivalently, the spectrum has sharp supremum `1 / sqrt 5`.  The fourth clause
identifies the all-one golden tail as an attaining point. -/
theorem rational_tower_hardness_spectrum :
    (forall (X : Type) (beta : X -> Real), hardnessSpectrum beta = Set.range beta) /\
      (forall (X : Type) (beta : X -> Real) (x : X),
        BadlyApproximable beta x <-> 0 < beta x) /\
      IsLeast (upperBounds (hardnessSpectrum rationalHardness)) (1 / Real.sqrt 5) /\
      rationalHardness goldenRatioPoint = 1 / Real.sqrt 5 := by
  constructor
  · intro X beta
    simp [hardnessSpectrum]
  constructor
  · intro X beta x
    simp [BadlyApproximable]
  constructor
  · constructor
    · intro value hvalue
      rcases hvalue with ⟨point, hpoint⟩
      rw [<- hpoint]
      exact rational_hardness_le_hurwitz point
    · intro value hvalue
      have hgolden := hvalue (Set.mem_range_self goldenRatioPoint)
      rwa [golden_ratio_hardness] at hgolden
  · exact golden_ratio_hardness

end

end D5.S0.Tower.Hardness.RationalSpectrum
