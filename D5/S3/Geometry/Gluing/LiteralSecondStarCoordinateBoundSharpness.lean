/- GID: D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBoundSharpness
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/LiteralSecondStarCoordinateBoundSharpness
   mirror-E: none(waiver:literal-standard-star-sharpness-core)
   anchors: []
   utility: none
   digest: The literal standard second closed star attains the sharp 25/48 coordinate bound. -/

import D5.S3.Geometry.Gluing.LiteralSecondStarCoordinateBound
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
open D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar
open D5.S3.Geometry.Gluing.LiteralSecondStarCoordinateBound

namespace D5.S3.Geometry.Gluing.LiteralSecondStarCoordinateBoundSharpness

private lemma prefix_coordinate_perm
    (π : Equiv.Perm (Fin 4)) (k l : Fin 4) :
    (barycenter standardVertices (prefixFace π k)) (π l) =
      if l ≤ k then (((k.val + 1 : ℕ) : ℝ)⁻¹) else 0 := by
  have hne : ∀ {a b : Fin 4}, a ≠ b → π a ≠ π b := by
    intro a b hab h
    exact hab (π.injective h)
  rw [prefix_barycenters]
  fin_cases k <;> fin_cases l <;> simp [standardVertices, hne]

private lemma parent_flag_affineIndependent (π : Equiv.Perm (Fin 4)) :
    AffineIndependent ℝ
      (fun k => barycenter standardVertices (prefixFace π k)) := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hv] at huv
  have h0 := congrArg (fun z => z (π 0)) huv
  have h1 := congrArg (fun z => z (π 1)) huv
  have h2 := congrArg (fun z => z (π 2)) huv
  have h3 := congrArg (fun z => z (π 3)) huv
  simp_rw [Finset.sum_apply, Pi.smul_apply] at h0 h1 h2 h3
  simp_rw [prefix_coordinate_perm] at h0 h1 h2 h3
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3
  ext k
  fin_cases k
  · change u 0 = v 0
    linarith
  · change u 1 = v 1
    linarith
  · change u 2 = v 2
    linarith
  · change u 3 = v 3
    linarith

private lemma prefix_coordinate
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) (hπ : π 0 = i) (k : Fin 4) :
    (barycenter standardVertices (prefixFace π k)) i =
      (((k.val + 1 : ℕ) : ℝ)⁻¹) := by
  have hne : ∀ {a b : Fin 4}, a ≠ b → π a ≠ π b := by
    intro a b hab h
    exact hab (π.injective h)
  have hi1 : i ≠ π 1 := by
    rw [← hπ]
    exact hne (by decide)
  have hi2 : i ≠ π 2 := by
    rw [← hπ]
    exact hne (by decide)
  have hi3 : i ≠ π 3 := by
    rw [← hπ]
    exact hne (by decide)
  rw [prefix_barycenters]
  fin_cases k <;> simp [standardVertices, hπ, hi1, hi2, hi3]

theorem literal_standard_closed_star_coordinate_bound_sharp (i : Fin 4) :
    ∃ x ∈ literalClosedStar standardVertices i, x i = (25 : ℝ) / 48 := by
  let π : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  have hπ : π 0 = i := by
    simp [π, Equiv.swap_apply_def]
  let q : Fin 4 → (Fin 4 → ℝ) :=
    fun k => barycenter standardVertices (prefixFace π k)
  let β : Fin 4 → ℝ := fun _ => (1 / 4 : ℝ)
  let x : Fin 4 → ℝ := barycenter q (Finset.univ : Finset (Fin 4))
  have hβnonneg : ∀ j, 0 ≤ β j := by
    intro j
    simp [β]
  have hβsum : ∑ j, β j = 1 := by
    norm_num [β, Fin.sum_univ_succ]
  have hxrepr : x = ∑ j, β j • q j := by
    calc
      x = ∑ j, faceWeight (Finset.univ : Finset (Fin 4)) j • q j := by
        simpa [x] using
          (barycenter_eq_sum q (Finset.univ : Finset (Fin 4)))
      _ = ∑ j, β j • q j := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        simp [β, faceWeight]
  have hqaff : AffineIndependent ℝ q := by
    simpa [q] using parent_flag_affineIndependent π
  have hqstar : x ∈ closedStar q := by
    apply ((actual_closed_and_open_star_iff q hqaff β hβnonneg hβsum x hxrepr).1).2
    intro j hj
    simp [β]
  have hliteral : x ∈ literalClosedStar standardVertices i := by
    exact ((literal_second_closed_and_open_star_iff
      standardVertices standardVertices_affineIndependent i x).1).2
      ⟨π, hπ, hqstar⟩
  refine ⟨x, hliteral, ?_⟩
  have hxi := congrArg (fun v => v i) hxrepr
  simp only [Finset.sum_apply, Pi.smul_apply] at hxi
  have hqcoord : ∀ k, q k i = (((k.val + 1 : ℕ) : ℝ)⁻¹) := by
    intro k
    exact prefix_coordinate π i hπ k
  simp_rw [hqcoord] at hxi
  norm_num [β, Fin.sum_univ_succ] at hxi ⊢
  linarith

end D5.S3.Geometry.Gluing.LiteralSecondStarCoordinateBoundSharpness
