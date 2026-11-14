/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeCompactBase
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeCompactBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed salient finite real cones admit positive compact-base functionals. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A positive normalization is constructed from the original cone by separation. -/

noncomputable section

open Set Filter
open scoped Topology Pointwise

namespace D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_positive_functional (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) :
    ∃ u : E →L[ℝ] ℝ, ∀ x ∈ C, x ≠ 0 → 0 < u x := by
  classical
  let S : Set E := {x | x ∈ C ∧ ‖x‖ = 1}
  have hS : IsCompact S := by
    convert (isCompact_sphere (0 : E) 1).inter_left C.isClosed using 1
    ext x
    simp [S]
  have hsep : ∀ x : S, ∃ f : E →L[ℝ] ℝ,
      (∀ y ∈ C, 0 ≤ f y) ∧ 0 < f x := by
    intro x
    have hx0 : (x : E) ≠ 0 := by
      intro h
      have hh := x.property.2
      simpa [h] using hh
    have hnot : -(x : E) ∉ C := hs _ x.property.1 hx0
    obtain ⟨f, hf, hfx⟩ := C.hyperplane_separation_point hnot
    refine ⟨f, hf, ?_⟩
    simpa only [map_neg, neg_lt_zero] using hfx
  choose F hF hFx using hsep
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun i : S => {y | 0 < F i y})
    (fun i => isOpen_lt continuous_const (F i).continuous) (by
      intro y hy
      simp only [mem_iUnion, mem_ofPred_eq]
      exact ⟨⟨y, hy⟩, hFx ⟨y, hy⟩⟩)
  let u : E →L[ℝ] ℝ := ∑ i ∈ t, F i
  have hu : ∀ y, u y = ∑ i ∈ t, F i y := by
    intro y
    simp [u]
  refine ⟨u, ?_⟩
  intro y hy hy0
  let z : E := ‖y‖⁻¹ • y
  have hz : z ∈ S := by
    refine ⟨C.smul_mem hy (inv_nonneg.mpr (norm_nonneg y)), ?_⟩
    simp [z, norm_smul, norm_ne_zero_iff.mpr hy0]
  obtain ⟨i, hi, hiz⟩ : ∃ i ∈ t, 0 < F i z := by
    have hh := ht hz
    simp only [mem_iUnion, mem_ofPred_eq] at hh
    rcases hh with ⟨i, hi, hiz⟩
    exact ⟨i, hi, hiz⟩
  have hupos : 0 < u z := by
    rw [hu]
    exact Finset.sum_pos' (fun j hj => hF j z hz.1) ⟨i, hi, hiz⟩
  have hh : 0 < ‖y‖⁻¹ * u y := by simpa [z, map_smul] using hupos
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hy0))).mp hh

private theorem exists_positive_compact_base (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) :
    ∃ u : E →L[ℝ] ℝ, (∀ x ∈ C, x ≠ 0 → 0 < u x) ∧
      IsCompact {x : E | x ∈ C ∧ u x = 1} ∧
      Convex ℝ {x : E | x ∈ C ∧ u x = 1} := by
  obtain ⟨u, hu⟩ := exists_positive_functional C hs
  refine ⟨u, hu, ?_, ?_⟩
  · exact D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base_compact C.isClosed hu
  · exact D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base_convex
      C.toPointedCone u.toLinearMap

private def baseProjection (u : E →L[ℝ] ℝ) (b : E) (hb : u b = 1) :
    E → u.ker := fun y => ⟨y - u y • b, by simp [hb]⟩

private theorem baseProjection_continuous (u : E →L[ℝ] ℝ) (b : E) (hb : u b = 1) :
    Continuous (baseProjection u b hb) := by
  exact (continuous_id.sub (u.continuous.smul continuous_const)).subtype_mk _

/-- The translated kernel chart has exactly the original cone interior and frontier. -/
private theorem base_chart_geometry (C : ProperCone ℝ E) (u : E →L[ℝ] ℝ)
    (b : E) (hb : u b = 1) :
    let K : Set u.ker := {v | b + (v : E) ∈ C}
    (∀ v : u.ker, v ∈ interior K ↔ b + (v : E) ∈ interior (C : Set E)) ∧
    (∀ v : u.ker, v ∈ frontier K ↔ b + (v : E) ∈ frontier (C : Set E)) := by
  dsimp only
  let K : Set u.ker := {v | b + (v : E) ∈ C}
  have hj : Continuous (fun v : u.ker => b + (v : E)) :=
    continuous_const.add continuous_subtype_val
  have hK : IsClosed K := C.isClosed.preimage hj
  have hint : ∀ v : u.ker,
      v ∈ interior K ↔ b + (v : E) ∈ interior (C : Set E) := by
    intro v
    have huv : u (b + (v : E)) = 1 := by simp [hb, v.property]
    constructor
    · intro hv
      let N : E → u.ker := fun y => (u y)⁻¹ • baseProjection u b hb y
      have hN : ContinuousAt N (b + (v : E)) := by
        exact (u.continuous.continuousAt.inv₀ (by rw [huv]; norm_num)).smul
          (baseProjection_continuous u b hb).continuousAt
      have hNv : N (b + (v : E)) = v := by
        apply Subtype.ext
        simp [N, baseProjection, huv]
      have hn : ∀ᶠ y in 𝓝 (b + (v : E)), N y ∈ K :=
        hN (by simpa [hNv] using mem_interior_iff_mem_nhds.mp hv)
      have hp : ∀ᶠ y in 𝓝 (b + (v : E)), 0 < u y :=
        (isOpen_lt continuous_const u.continuous).mem_nhds (by simp [huv])
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hn, hp] with y hy hypos
      have heq : u y • (b + ((N y : u.ker) : E)) = y := by
        change u y • (b + (u y)⁻¹ • (y - u y • b)) = y
        rw [smul_add, smul_smul, mul_inv_cancel₀ hypos.ne', one_smul]
        abel
      rw [← heq]
      exact C.smul_mem hy hypos.le
    · intro hv
      exact mem_interior_iff_mem_nhds.mpr
        (hj.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hv))
  refine ⟨hint, ?_⟩
  intro v
  rw [hK.frontier_eq, C.isClosed.frontier_eq]
  exact and_congr Iff.rfl (not_congr (hint v))

private theorem exists_full_compact_base [Nontrivial E] (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) (hfull : (interior (C : Set E)).Nonempty) :
    ∃ (u : E →L[ℝ] ℝ) (b : E),
      (∀ x ∈ C, x ≠ 0 → 0 < u x) ∧ u b = 1 ∧ b ∈ interior (C : Set E) ∧
      IsCompact {v : u.ker | b + (v : E) ∈ C} ∧
      (interior {v : u.ker | b + (v : E) ∈ C}).Nonempty ∧
      (∀ v : u.ker, v ∈ interior {v : u.ker | b + (v : E) ∈ C} ↔
        b + (v : E) ∈ interior (C : Set E)) ∧
      (∀ v : u.ker, v ∈ frontier {v : u.ker | b + (v : E) ∈ C} ↔
        b + (v : E) ∈ frontier (C : Set E)) := by
  obtain ⟨u, hu, hcompact, _⟩ := exists_positive_compact_base C hs
  obtain ⟨a, ha⟩ := hfull
  obtain ⟨a, ha, ha0⟩ : ∃ a : E, a ∈ interior (C : Set E) ∧ a ≠ 0 := by
    by_cases h : a = 0
    · subst a
      have hn : ∀ᶠ x in 𝓝[≠] (0 : E), x ∈ interior (C : Set E) :=
        nhdsWithin_le_nhds (isOpen_interior.mem_nhds ha)
      exact (hn.and self_mem_nhdsWithin).exists
    · exact ⟨a, ha, h⟩
  have hua : 0 < u a := hu a (interior_subset ha) ha0
  let b : E := (u a)⁻¹ • a
  have hub : u b = 1 := by simp [b, map_smul, hua.ne']
  have hbi : b ∈ interior (C : Set E) := by
    have hsub : (u a)⁻¹ • (C : Set E) ⊆ (C : Set E) := by
      rintro _ ⟨x, hx, rfl⟩
      exact C.smul_mem hx (inv_nonneg.mpr hua.le)
    apply interior_mono hsub
    rw [interior_smul₀ (inv_ne_zero hua.ne')]
    exact ⟨a, ha, rfl⟩
  have himage : baseProjection u b hub '' {x : E | x ∈ C ∧ u x = 1} =
      {v : u.ker | b + (v : E) ∈ C} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [baseProjection, hx.2] using hx.1
    · intro hv
      refine ⟨b + (v : E), ⟨hv, by simp [hub, v.property]⟩, ?_⟩
      apply Subtype.ext
      simp [baseProjection, hub, v.property]
  obtain ⟨hint, hfront⟩ := base_chart_geometry C u b hub
  refine ⟨u, b, hu, hub, hbi, ?_, ?_, hint, hfront⟩
  · rw [← himage]
    exact hcompact.image (baseProjection_continuous u b hub)
  · exact ⟨0, (hint 0).mpr (by simpa using hbi)⟩

end D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
