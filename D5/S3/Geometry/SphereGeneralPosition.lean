/- GID: D5/S3/Geometry/SphereGeneralPosition
   generality: G
   mirror-B: D5/B/S3/Geometry/SphereGeneralPosition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.AffineSpace.Independent]
   utility: none
   digest: Arbitrarily large finite affine-general-position sets on a round sphere. -/
module

public import D5.S3.Geometry.SphereSectionAvoidance
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Classical affine general position on spheres, constructed by finite
induction from proper-section avoidance. The dimension bound concerns the
linear carrier, so a sphere in dimension `d` admits independent subsets of
size at most `d+1`. -/

noncomputable section
public section

open Set Metric
open scoped InnerProductSpace

namespace D5.S3.Geometry.SphereGeneralPosition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Proper affine subspaces miss every nonempty open sphere patch, jointly
for any finite family. Nonempty subspaces are converted to genuine proper
affine hyperplanes by choosing nonzero perpendicular normals. -/
theorem exists_on_sphere_avoiding_affine_subspaces (hd : 2 ≤ Module.finrank ℝ E)
    {r : ℝ} (hr : 0 < r) {U : Set E} (hU : IsOpen U)
    (hpatch : ∃ x ∈ U, ‖x‖ = r) {ι : Type*} [Finite ι]
    (S : ι → AffineSubspace ℝ E) (hS : ∀ i, S i ≠ ⊤) :
    ∃ y ∈ U, ‖y‖ = r ∧ ∀ i, y ∉ S i := by
  classical
  let J := {i : ι // (S i : Set E).Nonempty}
  have hnormal (j : J) : ∃ a : E, ∃ b : ℝ,
      a ≠ 0 ∧ ∀ y ∈ S j.val, ⟪a, y⟫_ℝ = b := by
    obtain ⟨p, hp⟩ := j.property
    have hdir : (S j.val).direction ≠ ⊤ := by
      intro h
      exact hS j.val ((AffineSubspace.direction_eq_top_iff_of_nonempty j.property).mp h)
    have hperp : (S j.val).directionᗮ ≠ ⊥ := by
      intro h
      exact hdir (Submodule.orthogonal_eq_bot_iff.mp h)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    refine ⟨a, ⟪a, p⟫_ℝ, ha0, fun y hy => ?_⟩
    have h := Submodule.inner_left_of_mem_orthogonal
      (AffineSubspace.vsub_mem_direction hy hp) ha
    change ⟪a, y - p⟫_ℝ = 0 at h
    rw [inner_sub_right] at h
    exact sub_eq_zero.mp h
  choose a b ha hab using hnormal
  obtain ⟨y, hyU, hyr, hy⟩ :=
    SphereSectionAvoidance.exists_on_sphere_avoiding_sections hd hr hU hpatch a b ha
  refine ⟨y, hyU, hyr, fun i hi => ?_⟩
  exact hy ⟨i, ⟨y, hi⟩⟩ (hab ⟨i, ⟨y, hi⟩⟩ y hi)

/-- Any prescribed finite cardinality occurs on a positive-radius sphere
with every subset of at most `dim(E)+1` points affinely independent. In
particular this constructs the finite general-position configurations on
the two- and three-spheres used by faithful bipartite realizations. -/
theorem exists_sphere_general_position (hd : 2 ≤ Module.finrank ℝ E)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∃ s : Finset E, s.card = n ∧ (∀ x ∈ s, ‖x‖ = r) ∧
      ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank ℝ E + 1 →
        AffineIndepOn ℝ id (t : Set E) := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, rfl, by simp, ?_⟩
    intro t ht _
    have ht0 : t = ∅ := Finset.subset_empty.mp ht
    simp [ht0, affineIndepOn_empty]
  | succ n ih =>
    obtain ⟨s, hcard, hnorm, hind⟩ := ih
    let T := s.powerset.filter (fun t => t.card ≤ Module.finrank ℝ E)
    have hT (t : T) : affineSpan ℝ (t.val : Set E) ≠ ⊤ := by
      have hc := (Finset.mem_filter.mp t.property).2
      have hc' : (t.val : Set E).encard ≤ Module.finrank ℝ E := by exact_mod_cast hc
      simpa using affineSpan_image_ne_top_of_encard_le_finrank ℝ
        t.val.finite_toSet hc' (id : E → E)
    letI : Nontrivial E := Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank ℝ E)
    obtain ⟨x, hxr⟩ := exists_norm_eq E hr.le
    obtain ⟨y, _, hyr, hy⟩ := exists_on_sphere_avoiding_affine_subspaces hd hr isOpen_univ
      ⟨x, Set.mem_univ _, hxr⟩ (fun t : T => affineSpan ℝ (t.val : Set E)) hT
    have hys : y ∉ s := by
      intro hys
      have hsingle : ({y} : Finset E) ∈ T := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr (by simpa using hys), by simpa using (by omega : 1 ≤ Module.finrank ℝ E)⟩
      exact hy ⟨{y}, hsingle⟩ (mem_affineSpan ℝ (by simp))
    refine ⟨insert y s, by simp [hys, hcard], ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hyr
      · exact hnorm z hz
    · intro t ht htc
      by_cases hyt : y ∈ t
      · let u := t.erase y
        have hus : u ⊆ s := by
          intro z hz
          have hz' := Finset.mem_erase.mp hz
          rcases Finset.mem_insert.mp (ht hz'.2) with rfl | hzs
          · exact (hz'.1 rfl).elim
          · exact hzs
        have huc : u.card ≤ Module.finrank ℝ E := by
          have hc := Finset.card_erase_add_one hyt
          dsimp only [u]
          omega
        have huT : u ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hus, huc⟩
        have hi := (hind u hus (by omega)).id_insert (hy ⟨u, huT⟩)
        simpa only [u, ← Finset.coe_insert, Finset.insert_erase hyt] using hi
      · apply hind t ?_ htc
        intro z hz
        rcases Finset.mem_insert.mp (ht hz) with rfl | hzs
        · exact (hyt hz).elim
        · exact hzs

end D5.S3.Geometry.SphereGeneralPosition
