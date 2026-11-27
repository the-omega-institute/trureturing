/- GID: D5/S3/Topology/RelativeConeRigidity
   generality: G
   mirror-B: D5/B/S3/Topology/RelativeConeRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Distinct facet tips give the relative cone base contiguity rigidity at every depth. -/

import D5.S3.Topology.RelativeDerivedContiguity
import D5.S3.Topology.BarycentricBaseRigidity
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import OmegaBuild.Commands

/-! # Contiguity rigidity of the relatively subdivided cone

Each maximal retained facet has one strict coface with its own exterior tip.
The intersection of the incident facets controls old vertices, and the distinct
tips of two incident facets exclude exterior vertices.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Topology.RelativeConeRigidity

open D5.S3.Topology.RelativeDerivedContiguity
open D5.S3.Topology.BarycentricBaseRigidity
open D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open BarycentricGraphDistance

universe u

variable {V : Type u}

noncomputable section

local instance classicalDecEq (X : Type*) : DecidableEq X := Classical.decEq X

def oldImage {K A : PreAbstractSimplicialComplex V} (F : Face A) :
    Finset (V ⊕ OutsideFace K A) := F.val.disjSum ∅

def outsideBarycenter {K A : PreAbstractSimplicialComplex V} (c : OutsideFace K A) :
    V ⊕ OutsideFace K A := Sum.inr c

private theorem oldImage_mem_retainedBase {K A : PreAbstractSimplicialComplex V}
    (F : Face A) : oldImage F ∈ retainedBase K A := by
  change ∃ t ∈ A, t.image (Sum.inl : V → V ⊕ OutsideFace K A) = oldImage F
  exact ⟨F.val, F.property, (Finset.map_eq_image Function.Embedding.inl F.val).symm.trans
    (Finset.disjSum_empty F.val).symm⟩

theorem oldImage_mem_relativeDerived {K A : PreAbstractSimplicialComplex V}
    (F : Face A) : oldImage F ∈ relativeDerived K A := by
  exact retainedBase_le K A (oldImage_mem_retainedBase F)

theorem unique_strict_coface_of_maximal_retained
    {K A : PreAbstractSimplicialComplex V} (F : Face A) (hmax : IsMax F)
    {c : OutsideFace K A} (hFc : F.val ⊆ c.val)
    (hc : ∀ d : OutsideFace K A, F.val ⊆ d.val → d = c) :
    let s₀ := insert (outsideBarycenter c) (oldImage F)
    s₀ ∈ relativeDerived K A ∧ oldImage F ⊂ s₀ ∧
      ∀ s ∈ relativeDerived K A, oldImage F ⊂ s → s = s₀ := by
  intro s₀
  have hleft₀ : s₀.toLeft = F.val := by
    ext x
    simp [s₀, oldImage, outsideBarycenter]
  have hright₀ : s₀.toRight = ({c} : Finset (OutsideFace K A)) := by
    ext d
    simp [s₀, outsideBarycenter, oldImage]
  have hs₀ : s₀ ∈ relativeDerived K A := by
    refine ⟨?_, ?_⟩
    · exact Finset.Nonempty.mono (Finset.subset_insert _ _)
        (oldImage_mem_relativeDerived F |>.1)
    · refine ⟨?_, ?_, ?_⟩
      · intro _
        rw [hleft₀]
        exact F.property
      · rw [hright₀]
        simp
      · intro a ha
        rw [hright₀] at ha
        have hac : a = c := Finset.mem_singleton.mp ha
        subst a
        rw [hleft₀]
        exact hFc
  have hstrict : oldImage F ⊂ s₀ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_insert _ _, ?_⟩
    intro he
    have : outsideBarycenter c ∈ oldImage F := he ▸ Finset.mem_insert_self _ _
    simp [outsideBarycenter, oldImage] at this
  refine ⟨hs₀, hstrict, ?_⟩
  intro s hs hsub
  have hleft : oldImage F ⊆ s := hsub.1
  have hmem : s.toLeft ∈ A := by
    apply hs.2.1
    obtain ⟨x, hx⟩ := (A.isRelLowerSet_faces F.property).1
    refine ⟨x, Finset.mem_toLeft.mpr (hleft ?_)⟩
    simpa [oldImage] using hx
  have hFsub : F.val ⊆ s.toLeft := by
    intro x hx
    apply Finset.mem_toLeft.mpr
    apply hleft
    simp [oldImage, hx]
  have hmax' : (⟨s.toLeft, hmem⟩ : Face A) ≤ F :=
    hmax (b := (⟨s.toLeft, hmem⟩ : Face A)) hFsub
  have hle : s.toLeft ≤ F.val := hmax'
  have hleft_eq : s.toLeft = F.val := Finset.Subset.antisymm hle hFsub
  have hout : ∀ d ∈ (s.toRight : Set (OutsideFace K A)), d = c := by
    intro d hd
    apply hc d
    exact hleft_eq ▸ hs.2.2.2 d hd
  have hright : (s.toRight : Set (OutsideFace K A)) ⊆ ({c} : Set (OutsideFace K A)) := by
    intro d hd
    exact Set.mem_singleton_iff.mpr (hout d hd)
  have hright' : s.toRight ⊆ ({c} : Finset (OutsideFace K A)) := by
    intro d hd
    simpa using hright hd
  have hright_nonempty : c ∈ s.toRight := by
    by_contra hnc
    have : s = oldImage F := by
      rw [← Finset.toLeft_disjSum_toRight (u := s)]
      change s.toLeft.disjSum s.toRight = F.val.disjSum ∅
      rw [hleft_eq]
      apply congrArg (Finset.disjSum F.val)
      exact Finset.eq_empty_iff_forall_notMem.mpr (fun d hd =>
        hnc ((Finset.mem_singleton.mp (hright' hd)) ▸ hd))
    exact hsub.2 (this ▸ Finset.Subset.rfl)
  have hright_eq : s.toRight = {c} :=
    Finset.Subset.antisymm hright' (Finset.singleton_subset_iff.mpr hright_nonempty)
  rw [← Finset.toLeft_disjSum_toRight (u := s),
    ← Finset.toLeft_disjSum_toRight (u := s₀)]
  change s.toLeft.disjSum s.toRight = s₀.toLeft.disjSum s₀.toRight
  rw [hleft_eq, hright_eq, hleft₀, hright₀]

section Cone

variable [Fintype V]

def coneCarrier {A : PreAbstractSimplicialComplex V} (v : V)
    (hvA : Fresh v A) (F : Face A) : OutsideFace (cone v A) A :=
  ⟨insert v F.val, cone_face v (base_le_cone v A F.property), by
    intro hF
    exact hvA _ hF (Finset.mem_insert_self _ _)
  ⟩

theorem cone_carrier_contains_face {A : PreAbstractSimplicialComplex V} (v : V)
    (hvA : Fresh v A) (F : Face A) : F.val ⊆ (coneCarrier v hvA F).val := by
  intro x hx
  exact Finset.mem_insert_of_mem hx

theorem cone_unique_outside_carrier {A : PreAbstractSimplicialComplex V} (v : V)
    (hvA : Fresh v A) (F : Face A) (hmax : IsMax F) :
    ∀ d : OutsideFace (cone v A) A,
      F.val ⊆ d.val → d = coneCarrier v hvA F := by
  intro d hFd
  have hvd : v ∈ d.val := by
    by_contra hvd
    have he := d.property.1.2
    rw [Finset.erase_eq_of_notMem hvd] at he
    rcases he with he | he
    · exact d.property.1.1.ne_empty he
    · exact d.property.2 he
  have hne : (d.val.erase v).Nonempty := by
    obtain ⟨x, hx⟩ := (A.isRelLowerSet_faces F.property).1
    have hxv : x ≠ v := by
      intro hxv
      exact hvA F.val F.property (hxv ▸ hx)
    exact ⟨x, Finset.mem_erase.mpr ⟨hxv, hFd hx⟩⟩
  have hdA : d.val.erase v ∈ A := by
    rcases d.property.1.2 with he | he
    · exact (hne.ne_empty he).elim
    · exact he
  have hFerase : F.val ⊆ d.val.erase v :=
    Finset.subset_erase.mpr ⟨hFd, fun hv => hvA F.val F.property hv⟩
  have hdF : d.val.erase v ⊆ F.val := by
    have hmax' : (⟨d.val.erase v, hdA⟩ : Face A) ≤ F :=
      hmax (b := (⟨d.val.erase v, hdA⟩ : Face A)) hFerase
    exact hmax'
  have herase : d.val.erase v = F.val := Finset.Subset.antisymm hdF hFerase
  apply Subtype.ext
  change d.val = insert v F.val
  rw [← Finset.insert_erase hvd, herase]

/-- Distinct strict coface tips in a relative cone remain distinct after the
relative-derived construction. -/
theorem cone_distinct_carrier_tips {A : PreAbstractSimplicialComplex V} (v : V)
    (hvA : Fresh v A) {F G : Face A} (hFG : F ≠ G) :
    coneCarrier v hvA F ≠ coneCarrier v hvA G := by
  intro he
  have hfaces : insert v F.val = insert v G.val := congrArg Subtype.val he
  have hFsubG : F.val ⊆ G.val := by
    intro x hx
    have : x ∈ insert v G.val := hfaces ▸ Finset.mem_insert_of_mem hx
    rcases Finset.mem_insert.mp this with h | h
    · exact (hvA F.val F.property (h ▸ hx)).elim
    · exact h
  have hGsubF : G.val ⊆ F.val := by
    intro x hx
    have : x ∈ insert v F.val := hfaces.symm ▸ Finset.mem_insert_of_mem hx
    rcases Finset.mem_insert.mp this with h | h
    · exact (hvA G.val G.property (h ▸ hx)).elim
    · exact h
  apply hFG
  apply Subtype.ext
  exact Finset.Subset.antisymm hFsubG hGsubF


/-- The first relative-derived step gives each maximal cone-base face a unique
strict coface, obtained by adjoining the barycenter of its cone carrier. -/
theorem cone_first_relative_unique_coface
    {A : PreAbstractSimplicialComplex V} (v : V) (hvA : Fresh v A)
    (F : Face A) (hmax : IsMax F) :
    let s₀ := insert (outsideBarycenter (coneCarrier v hvA F)) (oldImage F)
    s₀ ∈ relativeDerived (cone v A) A ∧ oldImage F ⊂ s₀ ∧
      ∀ s ∈ relativeDerived (cone v A) A, oldImage F ⊂ s → s = s₀ :=
  unique_strict_coface_of_maximal_retained F hmax (cone_carrier_contains_face v hvA F)
    (cone_unique_outside_carrier v hvA F hmax)

end Cone

private def retainedFace {A : PreAbstractSimplicialComplex V}
    (K : PreAbstractSimplicialComplex V) (F : Face A) : Face (retainedBase K A) :=
  ⟨oldImage F, oldImage_mem_retainedBase F⟩

private theorem retainedFace_surjective {K A : PreAbstractSimplicialComplex V} :
    Function.Surjective (retainedFace (A := A) K) := by
  intro F
  have hF := F.property
  change ∃ t ∈ A, t.image (Sum.inl : V → V ⊕ OutsideFace K A) = F.val at hF
  obtain ⟨t, ht, he⟩ := hF
  refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
  change t.disjSum ∅ = F.val
  rwa [Finset.disjSum_empty, Finset.map_eq_image]

private theorem retainedFace_le_iff {K A : PreAbstractSimplicialComplex V} {F G : Face A} :
    retainedFace K F ≤ retainedFace K G ↔ F ≤ G := by
  change (oldImage (K := K) F ⊆ oldImage G) ↔ F.val ⊆ G.val
  simp [oldImage]

private theorem isMax_retainedFace_iff {K A : PreAbstractSimplicialComplex V} {F : Face A} :
    IsMax (retainedFace K F) ↔ IsMax F := by
  constructor
  · intro hF G hFG
    exact retainedFace_le_iff.mp (hF (retainedFace_le_iff.mpr hFG))
  · intro hF G hFG
    obtain ⟨G₀, rfl⟩ := retainedFace_surjective G
    exact retainedFace_le_iff.mpr (hF (retainedFace_le_iff.mp hFG))

private theorem exists_old_vertex {K A : PreAbstractSimplicialComplex V}
    (a : Vertex (retainedBase K A)) : ∃ a₀ : Vertex A, a.val = Sum.inl a₀.val := by
  let singleton : Face (retainedBase K A) := ⟨{a.val}, a.property⟩
  obtain ⟨F, hF⟩ := retainedFace_surjective singleton
  have hImage : oldImage F = {a.val} := congrArg Subtype.val hF
  obtain ⟨x, hx⟩ := (A.isRelLowerSet_faces F.property).1
  have hxImage : Sum.inl x ∈ (oldImage (K := K) F) := by simpa [oldImage] using hx
  have ha : Sum.inl x = a.val := Finset.mem_singleton.mp (hImage ▸ hxImage)
  have hxA := (A.isRelLowerSet_faces F.property).2
    (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
  exact ⟨⟨x, hxA⟩, ha.symm⟩

private abbrev Facet (A : PreAbstractSimplicialComplex V) := {F : Face A // IsMax F}

private def retainedFacet {A : PreAbstractSimplicialComplex V}
    (K : PreAbstractSimplicialComplex V) : Facet A ≃ Facet (retainedBase K A) :=
  Equiv.ofBijective
    (fun F => ⟨retainedFace K F.val, isMax_retainedFace_iff.mpr F.property⟩) <| by
    constructor
    · intro F G h
      have he : retainedFace K F.val = retainedFace K G.val := congrArg Subtype.val h
      exact Subtype.ext (le_antisymm (retainedFace_le_iff.mp he.le)
        (retainedFace_le_iff.mp he.ge))
    · rintro ⟨G, hG⟩
      obtain ⟨F, rfl⟩ := retainedFace_surjective G
      exact ⟨⟨F, isMax_retainedFace_iff.mp hG⟩, rfl⟩

private def UniqueFacetCarriers (K A : PreAbstractSimplicialComplex V) : Prop :=
  ∃ carrier : Facet A → OutsideFace K A, Function.Injective carrier ∧
    ∀ F : Facet A, F.val.val ⊆ (carrier F).val ∧
      ∀ d : OutsideFace K A, F.val.val ⊆ d.val → d = carrier F

private def FacetConditions (A : PreAbstractSimplicialComplex V) : Prop :=
  (∀ (a : Vertex A) (w : V),
    (∀ F : Face A, IsMax F → a.val ∈ F.val → w ∈ F.val) → w = a.val) ∧
  (∀ a : Vertex A, ∃ F G : Face A,
    IsMax F ∧ IsMax G ∧ F ≠ G ∧ a.val ∈ F.val ∧ a.val ∈ G.val)

private theorem relativeDerived_uniqueFacetCarriers {K A : PreAbstractSimplicialComplex V}
    (h : UniqueFacetCarriers K A) :
    UniqueFacetCarriers (relativeDerived K A) (retainedBase K A) := by
  obtain ⟨carrier, hinj, hcarrier⟩ := h
  have hcoface (F : Facet A) :=
    unique_strict_coface_of_maximal_retained F.val F.property (hcarrier F).1 (hcarrier F).2
  let nextCarrier (F : Facet A) : OutsideFace (relativeDerived K A) (retainedBase K A) :=
    ⟨insert (outsideBarycenter (carrier F)) (oldImage F.val), (hcoface F).1, by
      intro hbase
      have hmax : IsMax (retainedFace K F.val) := isMax_retainedFace_iff.mpr F.property
      have hsub : retainedFace K F.val ≤ ⟨_, hbase⟩ := (hcoface F).2.1.1
      exact (hcoface F).2.1.2 (hmax hsub)⟩
  have hinj' : Function.Injective nextCarrier := by
    intro F G he
    apply hinj
    have hfaces : (nextCarrier F).val = (nextCarrier G).val := congrArg Subtype.val he
    have htip : outsideBarycenter (carrier F) ∈ (nextCarrier G).val :=
      hfaces ▸ Finset.mem_insert_self _ _
    simpa [nextCarrier, outsideBarycenter, oldImage] using htip
  refine ⟨nextCarrier ∘ (retainedFacet K).symm,
    hinj'.comp (retainedFacet K).symm.injective, ?_⟩
  intro G
  obtain ⟨F, rfl⟩ := (retainedFacet K).surjective G
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  change oldImage F.val ⊆ (nextCarrier F).val ∧
    ∀ d : OutsideFace (relativeDerived K A) (retainedBase K A), oldImage F.val ⊆ d.val →
      d = nextCarrier F
  refine ⟨(hcoface F).2.1.1, fun d hsub => Subtype.ext ?_⟩
  apply (hcoface F).2.2 d.val d.property.1
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  exact d.property.2 (he ▸ oldImage_mem_retainedBase F.val)

private theorem retainedBase_facetConditions {K A : PreAbstractSimplicialComplex V}
    (h : FacetConditions A) : FacetConditions (retainedBase K A) := by
  constructor
  · intro a w hw
    obtain ⟨a₀, ha⟩ := exists_old_vertex a
    have hwold (F : Face A) (hF : IsMax F) (haF : a₀.val ∈ F.val) :
        w ∈ oldImage (K := K) F :=
      hw (retainedFace K F) (isMax_retainedFace_iff.mpr hF)
        (by simpa [ha, retainedFace, oldImage] using haF)
    cases w with
    | inl w =>
      rw [ha]
      apply congrArg Sum.inl
      exact h.1 a₀ w (fun F hF haF => by simpa [oldImage] using hwold F hF haF)
    | inr w =>
      obtain ⟨F, _, hF, _, _, haF, _⟩ := h.2 a₀
      have hmem := hwold F hF haF
      simp [oldImage] at hmem
  · intro a
    obtain ⟨a₀, ha⟩ := exists_old_vertex a
    obtain ⟨F, G, hF, hG, hne, haF, haG⟩ := h.2 a₀
    refine ⟨retainedFace K F, retainedFace K G,
      isMax_retainedFace_iff.mpr hF, isMax_retainedFace_iff.mpr hG, ?_, ?_, ?_⟩
    · intro he
      exact hne (le_antisymm (retainedFace_le_iff.mp he.le) (retainedFace_le_iff.mp he.ge))
    · simpa [ha, retainedFace, oldImage] using haF
    · simpa [ha, retainedFace, oldImage] using haG

private theorem relative_maximal_face_criterion {K A : PreAbstractSimplicialComplex V}
    (hintersection : ∀ (a : Vertex A) (w : V),
      (∀ F : Face A, IsMax F → a.val ∈ F.val → w ∈ F.val) → w = a.val)
    (htwo : ∀ a : Vertex A, ∃ F G : Face A,
      IsMax F ∧ IsMax G ∧ F ≠ G ∧ a.val ∈ F.val ∧ a.val ∈ G.val)
    (carrier : Facet A → OutsideFace K A) (hinj : Function.Injective carrier)
    (hcoface : ∀ F : Facet A, ∀ s ∈ relativeDerived K A, oldImage F.val ⊂ s →
      s = insert (outsideBarycenter (carrier F)) (oldImage F.val)) :
    MaximalFaceCriterion (relativeDerived K A) (retainedBase K A) := by
  intro a w hw
  obtain ⟨a₀, ha⟩ := exists_old_vertex a
  have hadjoin (F : Face A) (hmax : IsMax F) (haF : a₀.val ∈ F.val) :
      insert w (oldImage F) ∈ relativeDerived K A := by
    have hf := hw (retainedFace K F) (isMax_retainedFace_iff.mpr hmax)
      (by simpa [ha, retainedFace, oldImage] using haF)
    have hinsert : @insert _ _ (@Finset.instInsert _ (Classical.decEq _)) w
        (retainedFace K F).val = insert w (oldImage F) := by
      ext x
      simp only [Finset.mem_insert, retainedFace]
    exact hinsert ▸ hf
  cases w with
  | inl w =>
    rw [ha]
    apply congrArg Sum.inl
    apply hintersection a₀ w
    intro F hmax haF
    have hface := hadjoin F hmax haF
    have hleft : (insert (Sum.inl w) (oldImage (K := K) F)).toLeft = insert w F.val := by
      ext x
      simp [oldImage]
    have hmem : insert w F.val ∈ A := by
      have hnonempty : (insert (Sum.inl w) (oldImage (K := K) F)).toLeft.Nonempty := by
        rw [hleft]
        exact Finset.insert_nonempty _ _
      exact hleft ▸ hface.2.1 hnonempty
    have hle : (⟨insert w F.val, hmem⟩ : Face A) ≤ F :=
      hmax (b := ⟨insert w F.val, hmem⟩) (Finset.subset_insert _ _)
    exact hle (Finset.mem_insert_self _ _)
  | inr w =>
    have hwcarrier (F : Facet A) (haF : a₀.val ∈ F.val.val) : w = carrier F := by
      have hnot : Sum.inr w ∉ oldImage F.val := by simp [oldImage]
      have hstrict : oldImage F.val ⊂ insert (Sum.inr w) (oldImage F.val) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_insert _ _, ?_⟩
        intro he
        exact hnot (he ▸ Finset.mem_insert_self _ _)
      have he := hcoface F _ (hadjoin F.val F.property haF) hstrict
      have hwmem : Sum.inr w ∈ insert (outsideBarycenter (carrier F)) (oldImage F.val) :=
        he ▸ Finset.mem_insert_self _ _
      simpa [outsideBarycenter, oldImage] using hwmem
    obtain ⟨F, G, hF, hG, hne, haF, haG⟩ := htwo a₀
    have he : (⟨F, hF⟩ : Facet A) = ⟨G, hG⟩ :=
      hinj ((hwcarrier ⟨F, hF⟩ haF).symm.trans (hwcarrier ⟨G, hG⟩ haG))
    exact (hne (congrArg Subtype.val he)).elim

variable [Fintype V]

/-- The ambient complex and its retained base on their shared label type. -/
structure RelativePair where
  labels : Type u
  ambient : PreAbstractSimplicialComplex labels
  base : PreAbstractSimplicialComplex labels
  base_le : base ≤ ambient

/-- Iterated relative subdivisions of a cone along its retained base. -/
def relativeConeAtDepth (v : V) (A : PreAbstractSimplicialComplex V) : ℕ → RelativePair
  | 0 => ⟨V, cone v A, A, base_le_cone v A⟩
  | n + 1 =>
    let previous := relativeConeAtDepth v A n
    ⟨_, relativeDerived previous.ambient previous.base,
      retainedBase previous.ambient previous.base,
      retainedBase_le previous.ambient previous.base⟩

private theorem coneCarrier_injective {A : PreAbstractSimplicialComplex V}
    (v : V) (hvA : Fresh v A) :
    Function.Injective (fun F : Facet A => coneCarrier v hvA F.val) := by
  intro F G he
  apply Subtype.ext
  by_contra hne
  exact cone_distinct_carrier_tips v hvA hne he

private theorem relativeConeAtDepth_facetData {A : PreAbstractSimplicialComplex V}
    (v : V) (hvA : Fresh v A) (h : FacetConditions A) (n : ℕ) :
    UniqueFacetCarriers (relativeConeAtDepth v A n).ambient (relativeConeAtDepth v A n).base ∧
      FacetConditions (relativeConeAtDepth v A n).base := by
  induction n with
  | zero =>
    exact ⟨⟨fun F => coneCarrier v hvA F.val, coneCarrier_injective v hvA,
      fun F => ⟨cone_carrier_contains_face v hvA F.val,
        cone_unique_outside_carrier v hvA F.val F.property⟩⟩, h⟩
  | succ n ih =>
    exact ⟨relativeDerived_uniqueFacetCarriers ih.1, retainedBase_facetConditions ih.2⟩

/-- Intersections of incident base facets exclude other old vertices. Two such
facets have distinct exterior tips, excluding every exterior vertex. -/
theorem relative_cone_maximal_face_criterion
    {A : PreAbstractSimplicialComplex V} (v : V) (hvA : Fresh v A)
    (hintersection : ∀ (a : Vertex A) (w : V),
      (∀ F : Face A, IsMax F → a.val ∈ F.val → w ∈ F.val) → w = a.val)
    (htwo : ∀ a : Vertex A, ∃ F G : Face A,
      IsMax F ∧ IsMax G ∧ F ≠ G ∧ a.val ∈ F.val ∧ a.val ∈ G.val) :
    MaximalFaceCriterion (relativeDerived (cone v A) A) (retainedBase (cone v A) A) := by
  exact relative_maximal_face_criterion hintersection htwo (fun F => coneCarrier v hvA F.val)
    (coneCarrier_injective v hvA)
    (fun F => (cone_first_relative_unique_coface v hvA F.val F.property).2.2)

/-- After any positive number of relative subdivisions of a cone, every map
in the contiguity class of the base inclusion fixes each retained base vertex
at every common ordinary subdivision depth. -/
theorem relative_cone_all_depth_obstruction
    {A : PreAbstractSimplicialComplex V} (v : V) (hvA : Fresh v A)
    (hintersection : ∀ (a : Vertex A) (w : V),
      (∀ F : Face A, IsMax F → a.val ∈ F.val → w ∈ F.val) → w = a.val)
    (htwo : ∀ a : Vertex A, ∃ F G : Face A,
      IsMax F ∧ IsMax G ∧ F ≠ G ∧ a.val ∈ F.val ∧ a.val ∈ G.val) (t r : ℕ)
    {g : Vertex (baseAtDepth (relativeConeAtDepth v A (t + 1)).ambient
        (relativeConeAtDepth v A (t + 1)).base r) →
      Vertex (ambientAtDepth (relativeConeAtDepth v A (t + 1)).ambient r).2}
    (hchain : Relation.ReflTransGen Contiguous
      (includeVertex (baseAtDepth_le (relativeConeAtDepth v A (t + 1)).base_le r)) g)
    (a : Vertex (relativeConeAtDepth v A (t + 1)).base) :
    g (baseVertexAtDepth (relativeConeAtDepth v A (t + 1)).base_le r a) =
      includeVertex (baseAtDepth_le (relativeConeAtDepth v A (t + 1)).base_le r)
        (baseVertexAtDepth (relativeConeAtDepth v A (t + 1)).base_le r a) := by
  apply contiguity_chain_fixes_original_vertices _ ?_ r hchain a
  cases t with
  | zero => exact relative_cone_maximal_face_criterion v hvA hintersection htwo
  | succ t =>
    obtain ⟨⟨carrier, hinj, hcarrier⟩, hfacets⟩ :=
      relativeConeAtDepth_facetData v hvA ⟨hintersection, htwo⟩ (t + 1)
    exact relative_maximal_face_criterion hfacets.1 hfacets.2 carrier hinj (fun F =>
      (unique_strict_coface_of_maximal_retained F.val F.property
        (hcarrier F).1 (hcarrier F).2).2.2)

/--
info: 'D5.S3.Topology.RelativeConeRigidity.relative_cone_all_depth_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms relative_cone_all_depth_obstruction

end

end D5.S3.Topology.RelativeConeRigidity
