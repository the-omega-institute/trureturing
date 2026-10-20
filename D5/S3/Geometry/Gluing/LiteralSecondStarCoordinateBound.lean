/- GID: D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound
   mirror-E: none(waiver:literal-standard-star-coordinate-core)
   anchors: []
   utility: none
   digest: The literal standard second closed star inherits the sharp 25/48 coordinate lower bound. -/

import D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar
import D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
open D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar

namespace D5.S3.Geometry.Gluing.LiteralSecondStarCoordinateBound

noncomputable def standardVertices : Fin 4 → (Fin 4 → ℝ) :=
  fun i => Pi.single i 1

theorem standardVertices_affineIndependent :
    AffineIndependent ℝ standardVertices := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hv] at huv
  have h0 := congrArg (fun z => z 0) huv
  have h1 := congrArg (fun z => z 1) huv
  have h2 := congrArg (fun z => z 2) huv
  have h3 := congrArg (fun z => z 3) huv
  simp only [Finset.sum_apply, Pi.smul_apply] at h0 h1 h2 h3
  simp [standardVertices, Pi.single_apply] at h0 h1 h2 h3
  ext k
  fin_cases k
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

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

/- The literal second-star bridge supplies a parent flag. Expanding the parent
   convex combination into face weights makes its coordinate coefficients
   explicit, after which the sharp parent-star estimate applies. -/
theorem literal_standard_closed_star_coordinate_bound (i : Fin 4) (x : Fin 4 → ℝ)
    (hx : x ∈ literalClosedStar standardVertices i) :
    (25 : ℝ) / 48 ≤ x i := by
  have hiff := ((literal_second_closed_and_open_star_iff
    standardVertices standardVertices_affineIndependent i x).1).mp hx
  obtain ⟨π, hπ, hxstar⟩ := hiff
  let q : Fin 4 → (Fin 4 → ℝ) :=
    fun k => barycenter standardVertices (prefixFace π k)
  have hqaff : AffineIndependent ℝ q := by
    simpa [q] using parent_flag_affineIndependent π
  have hxstar_saved := hxstar
  obtain ⟨C, hinc, hmem⟩ := hxstar
  obtain ⟨I, hI, w, z, hw, hwone, hz, hzx⟩ :=
    mem_convexHull_iff_exists_fintype.mp hmem
  choose G hG hGz using hz
  let β : Fin 4 → ℝ := fun j => ∑ k, w k * faceWeight (G k) j
  have hβnonneg : ∀ j, 0 ≤ β j := by
    intro j
    dsimp [β]
    apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg (hw k)
    simp only [faceWeight]
    split_ifs <;> positivity
  have hβsum : ∑ j, β j = 1 := by
    classical
    dsimp [β]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, faceWeight_sum _ (C.face_nonempty _ (hG _))]
    simpa using hwone
  have hβeq : ∑ j, β j • q j = x := by
    classical
    calc
      ∑ j, β j • q j = ∑ k, w k • barycenter q (G k) := by
        simp only [β, Finset.sum_smul, mul_smul, barycenter_eq_sum, Finset.smul_sum]
        exact Finset.sum_comm
      _ = ∑ k, w k • z k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hGz k]
      _ = x := hzx
  have hdom : ∀ j, β j ≤ β 0 := by
    have hstar' :=
      (actual_closed_and_open_star_iff q hqaff β hβnonneg hβsum x hβeq.symm).1.mp
        hxstar_saved
    intro j
    by_cases hj : j = 0
    · subst j
      exact le_rfl
    · exact hstar' j hj
  have hbound :=
    (D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp).1
      β hβsum hdom
  have hxi := congrArg (fun v => v i) hβeq
  simp only [Finset.sum_apply, Pi.smul_apply] at hxi
  have hqcoord : ∀ k, q k i = (((k.val + 1 : ℕ) : ℝ)⁻¹) := by
    intro k
    exact prefix_coordinate π i hπ k
  simp_rw [hqcoord] at hxi
  norm_num [Fin.sum_univ_succ] at hxi
  linarith

end D5.S3.Geometry.Gluing.LiteralSecondStarCoordinateBound
