/- GID: D5/S3/Fourier/CompactWindowFiniteLocalComplexity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A discrete lift group meets every physical bounded ball times a compact internal window in finitely many points; consequently bounded displacement sets and pointed local patches of subsets of the model set are finite. -/

import Mathlib

/-!
Compactness and finite local complexity for discrete cut-and-project sets.
-/

namespace D5.S3.Fourier.CompactWindowFiniteLocalComplexity

open scoped Pointwise

variable {E H : Type*}
variable [NormedAddCommGroup E] [ProperSpace E]
variable [NormedAddCommGroup H]

/- The points of the model set are physical coordinates of lifts whose internal
coordinate lies in the window. -/
def modelSet (Γ : AddSubgroup (E × H)) (W : Set H) : Set E :=
  {x | ∃ h : H, (x, h) ∈ (Γ : Set (E × H)) ∧ h ∈ W}

def compactLift (Γ : AddSubgroup (E × H)) (K : Set H) (R : ℝ) : Set Γ :=
  {γ | (γ : E × H) ∈ Metric.closedBall 0 R ×ˢ K}

def displacementSet (Γ : AddSubgroup (E × H)) (K : Set H) (R : ℝ) : Set E :=
  (fun γ : Γ => ((γ : E × H).1)) '' compactLift Γ K R

def pointedPatch (S : Set E) (x : E) (R : ℝ) : Set E :=
  {z | ∃ y ∈ S, y ∈ Metric.closedBall x R ∧ z = y - x}

def pointedPatchFamily (S : Set E) (R : ℝ) : Set (Set E) :=
  {P | ∃ x ∈ S, P = pointedPatch S x R}

theorem compact_lift_finite (Γ : AddSubgroup (E × H)) [DiscreteTopology Γ]
    {K : Set H} (hK : IsCompact K) (R : ℝ) :
    (compactLift Γ K R).Finite := by
  have hball : IsCompact (Metric.closedBall (0 : E) R) :=
    isCompact_closedBall _ _
  have hproduct : IsCompact (Metric.closedBall (0 : E) R ×ˢ K) :=
    hball.prod hK
  have hclosed : IsClosed (Γ : Set (E × H)) :=
    Γ.isClosed_of_discreteTopology
  have hcompact : IsCompact (compactLift Γ K R) := by
    exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hproduct
  exact hcompact.finite_of_discrete

theorem displacement_finite (Γ : AddSubgroup (E × H)) [DiscreteTopology Γ]
    {K : Set H} (hK : IsCompact K) (R : ℝ) :
    (displacementSet Γ K R).Finite := by
  exact (compact_lift_finite Γ hK R).image _

theorem exists_uniform_positive_displacement_gap
    (Γ : AddSubgroup (E × H)) [DiscreteTopology Γ]
    {K : Set H} (hK : IsCompact K) (R : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ displacementSet Γ K R, x = 0 ∨ ε ≤ ‖x‖ := by
  let D := displacementSet Γ K R
  have hD : D.Finite := displacement_finite Γ hK R
  let Dpos : Set E := D \ ({0} : Set E)
  have hDpos : Dpos.Finite := hD.sdiff
  by_cases hne : Dpos.Nonempty
  · obtain ⟨x, hx, hxmin⟩ := Set.exists_min_image Dpos (fun y : E => ‖y‖) hDpos hne
    refine ⟨‖x‖, (norm_pos_iff.mpr ?_), ?_⟩
    · simpa only [Set.mem_singleton_iff] using hx.2
    · intro y hy
      rcases eq_or_ne y 0 with rfl | hyzero
      · exact Or.inl rfl
      · exact Or.inr (hxmin y ⟨hy, by simpa only [Set.mem_singleton_iff] using hyzero⟩)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    left
    by_contra hzero
    exact hne ⟨x, hx, by simpa only [Set.mem_singleton_iff] using hzero⟩

theorem window_difference_compact {W : Set H} (hW : IsCompact W) :
    IsCompact (W - W) := by
  rw [← Set.sub_image_prod]
  exact (hW.prod hW).image (continuous_fst.sub continuous_snd)

theorem pointedPatch_subset_displacement
    (Γ : AddSubgroup (E × H)) [DiscreteTopology Γ]
    {W : Set H} {T : Set E} (hS : T ⊆ modelSet Γ W)
    {x : E} (hx : x ∈ T) {R : ℝ} :
    pointedPatch T x R ⊆ displacementSet Γ (W - W) R := by
  rintro z ⟨y, hy, hyball, rfl⟩
  rcases hS hx with ⟨hx', hxΓ, hxW⟩
  rcases hS hy with ⟨hy', hyΓ, hyW⟩
  let γx : Γ := ⟨(x, hx'), hxΓ⟩
  let γy : Γ := ⟨(y, hy'), hyΓ⟩
  let γ : Γ := γy - γx
  have hγW : ((γ : E × H).2) ∈ W - W := by
    have hmem : hy' - hx' ∈ W - W :=
      (Set.mem_sub).2 ⟨hy', hyW, hx', hxW, rfl⟩
    simpa [γ, γx, γy] using hmem
  have hγball : (γ : E × H).1 ∈ Metric.closedBall 0 R := by
    simpa [γ, γx, γy, Metric.mem_closedBall, dist_eq_norm] using hyball
  exact ⟨γ, ⟨hγball, hγW⟩, by simp [γ, γx, γy]⟩

theorem pointedPatchFamily_finite
    (Γ : AddSubgroup (E × H)) [DiscreteTopology Γ]
    {W : Set H} {T : Set E} (hT : T ⊆ modelSet Γ W) {R : ℝ} (hW : IsCompact W) :
    (pointedPatchFamily T R).Finite := by
  let D := displacementSet Γ (W - W) R
  have hD : D.Finite := displacement_finite Γ (window_difference_compact hW) R
  refine hD.finite_subsets.subset ?_
  rintro P ⟨x, hx, rfl⟩
  exact pointedPatch_subset_displacement Γ hT hx

end D5.S3.Fourier.CompactWindowFiniteLocalComplexity
