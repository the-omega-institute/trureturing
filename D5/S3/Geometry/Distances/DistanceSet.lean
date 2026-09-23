/- GID: D5/S3/Geometry/Distances/DistanceSet
   generality: G
   mirror-B: D5/B/S3/Geometry/Distances/DistanceSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.GramMatrix]
   utility: none
   digest: Finite metric distance sets and the three-point bound for equilateral sets in the Euclidean plane. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false

namespace D5.S3.Geometry.Distances.DistanceSet

/-- The distances between distinct points of a finite set in a metric space. -/
def distanceSet {E : Type*} [MetricSpace E] (P : Finset E) : Set ℝ :=
  {r | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ dist x y = r}

/-- The number of distinct distances; finiteness follows from the finite set of pairs,
so no Euclidean or finite-dimensional hypothesis is needed. -/
noncomputable def distinctDistances {E : Type*} [MetricSpace E] (P : Finset E) : ℕ :=
  (show (distanceSet P).Finite from
    ((P.finite_toSet.prod P.finite_toSet).image (fun p : E × E => dist p.1 p.2)).subset
      (by
        rintro r ⟨x, hx, y, hy, _, rfl⟩
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩)).toFinset.card

/-- A finite set in the Euclidean plane with a common distance between every
two distinct points has at most three points. -/
theorem card_le_three_of_pairwise_dist_eq
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (r : ℝ)
    (h : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → dist x y = r) :
    P.card ≤ 3 := by
  classical
  by_contra hcard
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card_iff.mp (Nat.lt_of_not_ge hcard)
  have hr : 0 < r := (h a ha b hb hab) ▸ dist_pos.mpr hab
  let v : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![b - a, c - a, d - a]
  have hn : ∀ i, ‖v i‖ = r := by
    intro i
    fin_cases i
    · simpa [v, ← dist_eq_norm, dist_comm] using h a ha b hb hab
    · simpa [v, ← dist_eq_norm, dist_comm] using h a ha c hc hac
    · simpa [v, ← dist_eq_norm, dist_comm] using h a ha d hd had
  have hdiff : ∀ i j, i ≠ j → ‖v i - v j‖ = r := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | simpa [v, sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm] using h b hb c hc hbc
      | simpa [v, sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm] using h b hb d hd hbd
      | simpa [v, sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm] using h c hc d hd hcd
  have hg : ∀ i j, Matrix.gram ℝ v i j = if i = j then r ^ 2 else r ^ 2 / 2 := by
    intro i j
    rw [Matrix.gram_apply,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      hn i, hn j]
    split_ifs with hij
    · subst j
      simp [pow_two]
    · rw [hdiff i j hij]
      ring
  have hdet : (Matrix.gram ℝ v).det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp only [hg]
    norm_num [Fin.ext_iff]
    nlinarith [pow_pos hr 6]
  have hdim := (Matrix.linearIndependent_of_det_gram_ne_zero hdet).fintype_card_le_finrank
  norm_num at hdim

end D5.S3.Geometry.Distances.DistanceSet
