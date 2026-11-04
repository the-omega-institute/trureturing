/- GID: D5/S3/Geometry/CosphericalUnitLocus
   generality: G
   mirror-B: D5/B/S3/Geometry/CosphericalUnitLocus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional]
   utility: none
   digest: Common unit-distance loci of cospherical anchors are exact orthogonal spheres. -/
module

public import D5.S3.Geometry.SphereSectionAvoidance
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Classical orthogonal decomposition of the common sphere intersection.
The anchor family is nonempty through its specified base index; repeated
anchors and all carrier codimensions are allowed. -/

noncomputable section
public section

open Set Metric
open scoped InnerProductSpace

namespace D5.S3.Geometry.CosphericalUnitLocus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem unit_locus_iff {ι : Type*} (x : ι → E) (i₀ : ι)
    (W : Submodule ℝ E) (c : E) (r : ℝ)
    (hspan : Submodule.span ℝ (Set.range (fun i => x i - x i₀)) = W)
    (hmem : ∀ i, x i - c ∈ W) (hc : c ∈ Wᗮ) (hx : ∀ i, ‖x i‖ = r)
    (p : E) :
    (∀ i, dist p (x i) = 1) ↔
      p - c ∈ Wᗮ ∧ ‖p - c‖ ^ 2 = 1 - r ^ 2 + ‖c‖ ^ 2 := by
  have hdistance (hp : p ∈ Wᗮ) (i : ι) :
      dist p (x i) ^ 2 = ‖p - c‖ ^ 2 + r ^ 2 - ‖c‖ ^ 2 := by
    have hh := Submodule.inner_left_of_mem_orthogonal (hmem i) hp
    rw [inner_sub_right] at hh
    simp only [dist_eq_norm, norm_sub_sq_real, hx i]
    linarith
  constructor
  · intro h
    have hinner (i : ι) : ⟪p, x i - x i₀⟫_ℝ = 0 := by
      have hi := congrArg (fun t : ℝ => t ^ 2) (h i)
      have h0 := congrArg (fun t : ℝ => t ^ 2) (h i₀)
      simp only [dist_eq_norm, norm_sub_sq_real, hx] at hi h0
      rw [inner_sub_right]
      linarith
    have hker : W ≤ LinearMap.ker (innerSL ℝ p).toLinearMap := by
      rw [← hspan]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hinner i
    have hp : p ∈ Wᗮ := (W.mem_orthogonal' p).mpr (fun w hw => hker hw)
    refine ⟨Wᗮ.sub_mem hp hc, ?_⟩
    have hh := hdistance hp i₀
    rw [h i₀] at hh
    linarith
  · rintro ⟨hpc, hnorm⟩ i
    have hp : p ∈ Wᗮ := by simpa using Wᗮ.add_mem hpc hc
    have hh := hdistance hp i
    nlinarith [dist_nonneg (x := p) (y := x i)]

/-- The direction of the affine hull of the anchor family. -/
def anchorDirection {ι : Type*} (x : ι → E) (i₀ : ι) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i => x i - x i₀))

/-- The nearest-to-zero point of the anchor affine hull, constructed by
orthogonal projection of its chosen base point. -/
def anchorCenter [FiniteDimensional ℝ E] {ι : Type*} (x : ι → E) (i₀ : ι) : E :=
  x i₀ - (anchorDirection x i₀).starProjection (x i₀)

private theorem anchorCenter_mem_orthogonal [FiniteDimensional ℝ E]
    {ι : Type*} (x : ι → E) (i₀ : ι) :
    anchorCenter x i₀ ∈ (anchorDirection x i₀)ᗮ := by
  exact (anchorDirection x i₀).sub_starProjection_mem_orthogonal (x i₀)

private theorem sub_anchorCenter_mem [FiniteDimensional ℝ E]
    {ι : Type*} (x : ι → E) (i₀ i : ι) :
    x i - anchorCenter x i₀ ∈ anchorDirection x i₀ := by
  have h₁ : x i - x i₀ ∈ anchorDirection x i₀ :=
    Submodule.subset_span (Set.mem_range_self i)
  have h₂ : (anchorDirection x i₀).starProjection (x i₀) ∈ anchorDirection x i₀ := by
    rw [Submodule.starProjection_apply]
    exact Subtype.coe_prop _
  convert (anchorDirection x i₀).add_mem h₁ h₂ using 1
  dsimp [anchorCenter]
  abel

/-- The exact common-unit locus, with its center and carrier constructed
from the anchors themselves. This includes codimension-one two-point loci;
it asserts neither positive dimension nor the existence of a point. -/
theorem common_unit_locus_iff [FiniteDimensional ℝ E]
    {ι : Type*} (x : ι → E) (i₀ : ι) (r : ℝ) (hx : ∀ i, ‖x i‖ = r) (p : E) :
    (∀ i, dist p (x i) = 1) ↔
      p - anchorCenter x i₀ ∈ (anchorDirection x i₀)ᗮ ∧
        ‖p - anchorCenter x i₀‖ ^ 2 = 1 - r ^ 2 + ‖anchorCenter x i₀‖ ^ 2 :=
  unit_locus_iff x i₀ (anchorDirection x i₀) (anchorCenter x i₀) r rfl
    (sub_anchorCenter_mem x i₀) (anchorCenter_mem_orthogonal x i₀) hx p

/-- Every nonempty open patch of a positive-dimensional common-unit locus
admits simultaneous avoidance of finitely many forbidden unit distances and
collisions. A forbidden center is separated either by its norm or by the
anchor affine hull. The proper-section hypotheses are discharged here. -/
theorem exists_common_unit_avoiding [FiniteDimensional ℝ E]
    {ι : Type*} (x : ι → E) (i₀ : ι) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hx : ∀ i, ‖x i‖ = r)
    (hd : 2 ≤ Module.finrank ℝ (anchorDirection x i₀)ᗮ)
    {U : Set E} (hU : IsOpen U) (hpatch : ∃ p ∈ U, ∀ i, dist p (x i) = 1)
    {α β : Type*} [Finite α] [Finite β] (z : α → E) (q : β → E)
    (hz : ∀ j, ‖z j‖ ≠ r ∨ z j - anchorCenter x i₀ ∉ anchorDirection x i₀) :
    ∃ p ∈ U, (∀ i, dist p (x i) = 1) ∧
      (∀ j, dist p (z j) ≠ 1) ∧ ∀ j, p ≠ q j := by
  let W := anchorDirection x i₀
  let c := anchorCenter x i₀
  let R := Real.sqrt (1 - r ^ 2 + ‖c‖ ^ 2)
  have hs : 0 < 1 - r ^ 2 + ‖c‖ ^ 2 := by
    nlinarith [sq_nonneg ‖c‖, mul_pos (by linarith : 0 < 1 - r) (by linarith : 0 < 1 + r)]
  have hR : 0 < R := Real.sqrt_pos.mpr hs
  have hR2 : R ^ 2 = 1 - r ^ 2 + ‖c‖ ^ 2 := Real.sq_sqrt hs.le
  have hpatch' : ∃ w : Wᗮ, c + (w : E) ∈ U ∧ ‖w‖ = R := by
    obtain ⟨p, hpU, hp⟩ := hpatch
    have hl := (common_unit_locus_iff x i₀ r hx p).mp hp
    refine ⟨⟨p - c, hl.1⟩, ?_, ?_⟩
    · simpa using hpU
    · change ‖p - c‖ = R
      have hl2 : ‖p - c‖ ^ 2 = 1 - r ^ 2 + ‖c‖ ^ 2 := hl.2
      nlinarith [norm_nonneg (p - c)]
  have hproper (j : α) : Wᗮ.orthogonalProjectionOnto (z j - c) = 0 →
      R ^ 2 + ‖z j - c‖ ^ 2 ≠ 1 := by
    intro hproj heq
    have hzw : z j - c ∈ W := by
      have hzw' := Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hproj
      simpa only [Submodule.orthogonal_orthogonal] using hzw'
    have hcz : ⟪c, z j - c⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hzw (anchorCenter_mem_orthogonal x i₀)
    have hnorm := norm_add_sq_real c (z j - c)
    simp only [add_sub_cancel, hcz, mul_zero, add_zero] at hnorm
    have hn : ‖z j‖ = r := by nlinarith [norm_nonneg (z j)]
    rcases hz j with hj | hj
    · exact hj hn
    · exact hj hzw
  obtain ⟨w, hwU, hwR, hwz, hwq⟩ :=
    SphereSectionAvoidance.exists_on_affine_sphere_avoiding Wᗮ hd c hR hU hpatch' z q hproper
  refine ⟨c + (w : E), hwU, ?_, hwz, hwq⟩
  apply (common_unit_locus_iff x i₀ r hx _).mpr
  refine ⟨?_, ?_⟩
  · change c + (w : E) - c ∈ Wᗮ
    simpa only [add_sub_cancel_left] using w.property
  · change ‖c + (w : E) - c‖ ^ 2 = 1 - r ^ 2 + ‖c‖ ^ 2
    rw [add_sub_cancel_left]
    change ‖w‖ ^ 2 = 1 - r ^ 2 + ‖c‖ ^ 2
    rw [hwR]
    exact hR2

end D5.S3.Geometry.CosphericalUnitLocus
