/- GID: D5/S3/TotalVariation/FairBiasFacetQuotient
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasFacetQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The realized fair-bias complex has a quotient by the full facet boundaries. -/
import D5.S3.Geometry.FiniteAttachmentQuotient
import D5.S3.TotalVariation.FairBiasCriticalFacetCollapse

/-! The retained realization meets each omitted facet simplex in its full boundary. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.TotalVariation.FairBiasFacetQuotient

open Set Topology

open D5.S3.Geometry.FiniteAttachmentQuotient
open D5.S3.Geometry.FiniteConeCollapse
open D5.S3.Geometry.FiniteConeUnionWedge
open D5.S3.Geometry.FiniteCoordinateTruncation (support mem_support support_nonempty)
open D5.S3.Geometry.FiniteSimplicialJoin (Space realizationCompactSpace)
open D5.S3.TotalVariation.FairBiasCriticalFacetCollapse
open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasRestriction

open scoped ContinuousMap

universe geoA geoL
variable {A : Type geoA} {L : Type geoL} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

/-- The realized retained subcomplex as a subset of the full signed realization. -/
def coreSet (c : L → A) : Set (Space (signedComplex c)) :=
  {x | x.val ∈ realization (retainedComplex c)}

private theorem disk_le (c : L → A) (B : fullRestrictionFacets c) :
    simplexOn B.val ≤ signedComplex c := by
  rintro s ⟨hs, hsB⟩
  exact subface_of_facet c B.property.1 hs hsB

/-- The coordinate inclusion of a full-restriction facet's simplex. -/
def diskIn (c : L → A) (B : fullRestrictionFacets c) :
    C(Space (simplexOn B.val), Space (signedComplex c)) :=
  realizationInclusion (disk_le c B)

omit [Module (ZMod 2) A] [Finite A] in
private theorem disk_mem_faceSimplex (c : L → A) (B : fullRestrictionFacets c)
    (x : Space (simplexOn B.val)) : x.val ∈ faceSimplex B.val := by
  obtain ⟨s, hs, hx⟩ := (realization_mem_iff _ _).mp x.property
  obtain ⟨_, hsB⟩ : s.Nonempty ∧ s ⊆ B.val := hs
  exact ⟨hx.1, hx.2.1, fun v hv => hx.2.2 v (fun h => hv (hsB h))⟩

private theorem disk_inter_core (c : L → A) (B : fullRestrictionFacets c)
    (s : Finset (L × Bool)) :
    s ∈ retainedComplex c ⊓ simplexOn B.val ↔ s.Nonempty ∧ s ⊂ B.val := by
  change ((s ∈ signedComplex c ∧ s ∉ fullRestrictionFacets c) ∧
    (s.Nonempty ∧ s ⊆ B.val)) ↔ s.Nonempty ∧ s ⊂ B.val
  constructor
  · rintro ⟨⟨_, hsNot⟩, hs, hsB⟩
    exact ⟨hs, Finset.ssubset_iff_subset_ne.mpr ⟨hsB, fun h => hsNot (h.symm ▸ B.property)⟩⟩
  · rintro ⟨hs, hsB⟩
    have hsFace := disk_le c B (show s ∈ simplexOn B.val from ⟨hs, hsB.subset⟩)
    refine ⟨⟨hsFace, ?_⟩, hs, hsB.subset⟩
    intro h
    have hEq := (mem_facets.mp h.1).2 B.val (mem_facets.mp B.property.1).1 hsB.subset
    exact (Finset.ssubset_iff_subset_ne.mp hsB).2 hEq.symm

private theorem diskIn_mem_core_iff_boundary_realization (c : L → A)
    (B : fullRestrictionFacets c) (x : Space (simplexOn B.val)) :
    diskIn c B x ∈ coreSet c ↔ ∃ s : Finset (L × Bool),
      s.Nonempty ∧ s ⊂ B.val ∧ x.val ∈ faceSimplex s := by
  change x.val ∈ realization (retainedComplex c) ↔ _
  have hmem : x.val ∈ realization (retainedComplex c) ↔
      x.val ∈ realization (retainedComplex c) ∩ realization (simplexOn B.val) :=
    ⟨fun hx => ⟨hx, x.property⟩, And.left⟩
  rw [hmem, ← realization_intersection, realization_mem_iff]
  simp only [disk_inter_core, and_assoc]

/-- The attaching locus is the whole geometric boundary, including an empty
boundary when the facet has a single vertex. -/
theorem diskIn_mem_core_iff_boundary (c : L → A) (B : fullRestrictionFacets c)
    (x : Space (simplexOn B.val)) :
    diskIn c B x ∈ coreSet c ↔ ∃ v ∈ B.val, x.val v = 0 := by
  rw [diskIn_mem_core_iff_boundary_realization]
  constructor
  · rintro ⟨s, _, hs, hx⟩
    obtain ⟨v, hvB, hvs⟩ := Finset.exists_of_ssubset hs
    exact ⟨v, hvB, hx.2.2 v hvs⟩
  · rintro ⟨v, hv, hxv⟩
    have hx := disk_mem_faceSimplex c B x
    have hsub : support x.val ⊆ B.val := by
      intro w hw
      by_contra hn
      exact (mem_support _ _).mp hw (hx.2.2 w hn)
    have hproper : support x.val ⊂ B.val :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => (mem_support _ _).mp
        (h.symm ▸ hv) hxv⟩
    exact ⟨support x.val, support_nonempty ⟨hx.1, hx.2.1⟩, hproper,
      hx.1, hx.2.1, fun w hw => Classical.not_not.mp (fun h => hw ((mem_support _ _).mpr h))⟩

private theorem core_nonempty (c : L → A) (h : (facets c).Nonempty) :
    Nonempty (coreSet c) := by
  obtain ⟨B, hB, _, ⟨S⟩⟩ := exists_collapse_to_first_facet c h
  have hBne := ((signedComplex c).isRelLowerSet_faces (mem_facets.mp hB).1).1
  let p : Space (simplexOn B) :=
    ⟨Pi.single hBne.choose 1, ⟨B, ⟨hBne, Finset.Subset.refl _⟩,
      subset_convexHull ℝ _ ⟨hBne.choose, hBne.choose_spec, rfl⟩⟩⟩
  let q := realizationInclusion S.monotone p
  let hCore : retainedComplex c ≤ signedComplex c := fun _ hs => hs.1
  exact ⟨⟨realizationInclusion hCore q, q.property⟩⟩

private theorem disk_cover (c : L → A) (x : Space (signedComplex c)) :
    x ∈ coreSet c ∨ ∃ B d, diskIn c B d = x := by
  obtain ⟨s, hs, hx⟩ := x.property
  by_cases hf : s ∈ fullRestrictionFacets c
  · have hne := ((signedComplex c).isRelLowerSet_faces hs).1
    let d : Space (simplexOn s) := ⟨x.val, ⟨s, ⟨hne, Finset.Subset.refl _⟩, hx⟩⟩
    exact Or.inr ⟨⟨s, hf⟩, d, Subtype.ext rfl⟩
  · exact Or.inl ⟨s, ⟨hs, hf⟩, hx⟩

private theorem disk_overlap (c : L → A) {B D : fullRestrictionFacets c} (h : B ≠ D)
    (x : Space (simplexOn B.val)) (y : Space (simplexOn D.val))
    (he : diskIn c B x = diskIn c D y) : diskIn c B x ∈ coreSet c := by
  apply (diskIn_mem_core_iff_boundary c B x).mpr
  have hNotSub : ¬ B.val ⊆ D.val := by
    intro hsub
    have hEq := (mem_facets.mp B.property.1).2 D.val (mem_facets.mp D.property.1).1 hsub
    exact h (Subtype.ext hEq.symm)
  obtain ⟨v, hvB, hvD⟩ := Finset.not_subset.mp hNotSub
  have hcoord : x.val v = y.val v := congrArg (fun z : Space (signedComplex c) => z.val v) he
  exact ⟨v, hvB, hcoord.trans ((disk_mem_faceSimplex c D y).2.2 v hvD)⟩

/-- Collapsing the retained realization identifies precisely the common attaching
boundary of the facet disks and the added point. -/
theorem exists_core_attachment_homeomorph (c : L → A) (h : (facets c).Nonempty) :
    ∃ p : coreSet c, ∃ e : AttachedQuotient (diskIn c) (coreSet c) ≃ₜ Collapse (coreSet c),
      e (collapseMap (attachingSet (diskIn c) (coreSet c)) (Sum.inl ())) =
        collapseMap (coreSet c) p ∧
      ∀ B d, e (collapseMap (attachingSet (diskIn c) (coreSet c)) (Sum.inr ⟨B, d⟩)) =
        collapseMap (coreSet c) (diskIn c B d) := by
  let _ := realizationCompactSpace (signedComplex c)
  let _ (B : fullRestrictionFacets c) := realizationCompactSpace (simplexOn B.val)
  obtain ⟨p⟩ := core_nonempty c h
  refine ⟨p, exists_homeomorph (diskIn c) p
    ((realization_closed (retainedComplex c)).preimage continuous_subtype_val)
    (disk_cover c) ?_ ?_⟩
  · intro B x y hxy
    exact Subtype.ext (congrArg (fun z : Space (signedComplex c) => z.val) hxy)
  · intro B D hne x y he
    exact disk_overlap c hne x y he

end D5.S3.TotalVariation.FairBiasFacetQuotient
