/- GID: D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/SecondBarycentricCoordinateBound
   mirror-E: none(waiver:finite-rank-coordinate-core)
   anchors: []
   utility: none
   digest: The eight rank types in a second barycentric vertex give the sharp 25/48 coordinate bound. -/

import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound

noncomputable def rankWeight (r : Fin 4) : ℝ :=
  ((r.val + 1 : ℕ) : ℝ)⁻¹

noncomputable def rankAverage (J : Finset (Fin 4)) : ℝ :=
  (J.card : ℝ)⁻¹ * ∑ r ∈ J, rankWeight r

private lemma rank_average_lower_bound (J : Finset (Fin 4)) (h0 : (0 : Fin 4) ∈ J) :
    (25 : ℝ) / 48 ≤ rankAverage J := by
  classical
  by_cases h1 : (1 : Fin 4) ∈ J
  · by_cases h2 : (2 : Fin 4) ∈ J
    · by_cases h3 : (3 : Fin 4) ∈ J
      · have hJ : J = ({0, 1, 2, 3} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
      · have hJ : J = ({0, 1, 2} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
    · by_cases h3 : (3 : Fin 4) ∈ J
      · have hJ : J = ({0, 1, 3} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
      · have hJ : J = ({0, 1} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
  · by_cases h2 : (2 : Fin 4) ∈ J
    · by_cases h3 : (3 : Fin 4) ∈ J
      · have hJ : J = ({0, 2, 3} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
      · have hJ : J = ({0, 2} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
    · by_cases h3 : (3 : Fin 4) ∈ J
      · have hJ : J = ({0, 3} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]
      · have hJ : J = ({0} : Finset (Fin 4)) := by
          ext r
          fin_cases r <;> simp_all
        subst J
        norm_num [rankAverage, rankWeight]

private lemma rank_average_full :
    rankAverage (Finset.univ : Finset (Fin 4)) = (25 : ℝ) / 48 := by
  norm_num [rankAverage, rankWeight, Fin.sum_univ_succ]

private lemma parent_coordinate_lower_bound (β : Fin 4 → ℝ)
    (hs : ∑ j, β j = 1)
    (hdom : ∀ j, β j ≤ β 0) :
    (25 : ℝ) / 48 ≤ β 0 + (1 / 2 : ℝ) * β 1 +
      (1 / 3 : ℝ) * β 2 + (1 / 4 : ℝ) * β 3 := by
  have h1 : 0 ≤ β 0 - β 1 := sub_nonneg.mpr (hdom 1)
  have h2 : 0 ≤ β 0 - β 2 := sub_nonneg.mpr (hdom 2)
  have h3 : 0 ≤ β 0 - β 3 := sub_nonneg.mpr (hdom 3)
  have hsum : β 0 + β 1 + β 2 + β 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs
  linarith

/- The finite rank table is the arithmetic core of CFMP §69.3.  The second
   conjunct records the full-rank equality case, which is the sharpness witness;
   the first conjunct is the uniform bound for every rank set containing the
   original vertex rank. -/
theorem second_star_rank_coordinate_bound_and_sharp :
    (∀ J : Finset (Fin 4), (0 : Fin 4) ∈ J →
      (25 : ℝ) / 48 ≤ rankAverage J) ∧
    rankAverage (Finset.univ : Finset (Fin 4)) = (25 : ℝ) / 48 := by
  exact ⟨rank_average_lower_bound, rank_average_full⟩

/- The same constant is the sharp parent-star linear bound used after the
   literal second-star-to-parent-star reduction. -/
theorem parent_star_coordinate_bound_and_sharp :
    (∀ (β : Fin 4 → ℝ), ∑ j, β j = 1 →
      (∀ j, β j ≤ β 0) →
      (25 : ℝ) / 48 ≤ β 0 + (1 / 2 : ℝ) * β 1 +
        (1 / 3 : ℝ) * β 2 + (1 / 4 : ℝ) * β 3) ∧
    (25 : ℝ) / 48 = (1 / 4 : ℝ) + (1 / 2 : ℝ) * (1 / 4 : ℝ) +
      (1 / 3 : ℝ) * (1 / 4 : ℝ) + (1 / 4 : ℝ) * (1 / 4 : ℝ) := by
  constructor
  · intro β hs hdom
    exact parent_coordinate_lower_bound β hs hdom
  · norm_num

end D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound
