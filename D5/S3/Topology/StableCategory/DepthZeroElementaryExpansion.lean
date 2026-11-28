/- GID: D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/DepthZeroElementaryExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A categorical two-cover extends across an elementary expansion after two subdivisions. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteElementaryCollapse
import D5.S3.Topology.OrdinaryCollarRetraction
import D5.S3.Topology.StableCategory.DisjointContiguityGluing
import D5.S3.Topology.StableCategory.FourPieceCategoricalCover
import D5.S3.Topology.StableCategory.InducedCategoricalCover
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift

/-! An elementary expansion extends a categorical two-cover after two ordinary subdivisions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.DepthZeroElementaryExpansion

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd skeleton vertexOfFace)
open BarycentricNeighborhoodIteration (subdivision subdivision_full)
open D5.S3.Geometry.FiniteElementaryCollapse (CollapsePair)
open D5.S3.Topology.OrdinaryCollarRetraction (colourComplex)
open D5.S3.Topology.StableCategory.FourPieceCategoricalCover (CategoricalMapCover)
open D5.S3.Topology.StableCategory.OrdinaryContiguityLift
  (Simplicial includeSubcomplex include_subcomplex_simplicial ofTotal of_total_simplicial
    comp_chains constant_chain_of_reachable subdivide lift_chain)
open D5.S3.Topology.StableCategory.InducedCategoricalCover
  (has_categorical_cover_of_partition)
open ConnectedCategoryGraft (HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open DisjointContiguityGluing (glue_contiguity)
open Relation (ReflTransGen)
open private colourPiece glue from D5.S3.Topology.StableCategory.DisjointContiguityGluing
open private constant_face_image from D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private ofTotal_faceImage from
  D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private face_image_include constant_simplicial id_simplicial restrictFlag
  restrictFlag_simplicial subdivision_const from
  D5.S3.Topology.StableCategory.FourPieceCategoricalCover

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The old facet of the added simplex obtained by deleting `j`. -/
private def oldFacet (P : CollapsePair V) (j : V) : Finset V := P.upper.erase j

private theorem oldFacet_mem_retained (P : CollapsePair V) {j : V} (hj : j ∈ P.lower) :
    oldFacet P j ∈ P.retained := by
  have hapex : P.apex ∈ oldFacet P j := by
    have hne : P.apex ≠ j := fun h => P.apex_notMem (h ▸ hj)
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_insert_self _ _⟩
  have hsub : oldFacet P j ⊆ P.upper := Finset.erase_subset _ _
  have hambient : oldFacet P j ∈ P.ambient :=
    (P.ambient.isRelLowerSet_faces P.upper_mem).2 hsub ⟨P.apex, hapex⟩
  apply (P.mem_retained_iff _).2
  refine ⟨hambient, ?_, ?_⟩
  · intro h
    exact P.apex_notMem (h ▸ hapex)
  · intro h
    have he : j ∈ oldFacet P j := h.symm ▸ Finset.mem_insert_of_mem hj
    exact (Finset.mem_erase.mp he).1 rfl

private theorem missing_label_face
    {P : CollapsePair V} {P₁ : PreAbstractSimplicialComplex V} (T : Finset V)
    (hfacet₁ : ∀ {j : V}, j ∈ T → oldFacet P j ∈ P₁)
    {E : Finset V} (hE : E ∈ P.retained) (hEupper : E ⊆ P.upper)
    (hEnot₁ : E ∉ P₁) : T ⊆ E := by
  intro j hj
  by_contra hje
  have hEfacet : E ⊆ oldFacet P j := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hje (h ▸ hx), hEupper hx⟩
  have hfacet : oldFacet P j ∈ P₁ := hfacet₁ hj
  have hE₁ : E ∈ P₁ :=
    (P₁.isRelLowerSet_faces hfacet).2 hEfacet (P.retained.isRelLowerSet_faces hE).1
  exact hEnot₁ hE₁

private theorem missing_label_mem_piece_zero
    {P : CollapsePair V} {P₀ : PreAbstractSimplicialComplex V} (T : Finset V) (hTne : T.Nonempty)
    (hTle : T ⊆ P.lower)
    (hmixed : ∃ j ∈ P.lower, j ∉ T)
    (hfacet₀ : ∀ {j : V}, j ∈ P.lower → j ∉ T → oldFacet P j ∈ P₀) :
    T ∈ P₀ := by
  obtain ⟨j, hj, hjT⟩ := hmixed
  have hTupper : T ⊆ P.upper := hTle.trans (Finset.subset_insert _ _)
  have hTfacet : T ⊆ oldFacet P j := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hjT (h ▸ hx), hTupper hx⟩
  exact (P₀.isRelLowerSet_faces (hfacet₀ hj hjT)).2 hTfacet hTne

/-- The label on vertices of `sd K` used by the mixed construction.

  An old face receives label one when it lies in `P₁`. The two exceptional
  vertices `lower` and `upper` therefore receive label zero automatically.
-/
private def expansionLabel (P : CollapsePair V) (P₁ : PreAbstractSimplicialComplex V) :
    Face P.ambient → Fin 2 :=
  fun s => if s.val ∈ P₁ then 1 else 0

private def expansionColour (P : CollapsePair V) (P₁ : PreAbstractSimplicialComplex V)
    (i : Fin 2) : Face P.ambient → Bool :=
  fun s => decide (expansionLabel P P₁ s = i)

private abbrev zeroRegion (P : CollapsePair V) (P₁ : PreAbstractSimplicialComplex V) :=
  colourComplex (sd P.ambient) (expansionColour P P₁ 0)

private abbrev oneRegion (P : CollapsePair V) (P₁ : PreAbstractSimplicialComplex V) :=
  colourComplex (sd P.ambient) (expansionColour P P₁ 1)

private theorem one_region_le_subdivision
    (P : CollapsePair V) {P₁ : PreAbstractSimplicialComplex V} :
    oneRegion P P₁ ≤ BarycentricNeighborhoodIteration.subdivision P.ambient P₁ := by
  intro s hs
  refine ⟨hs.1.1, hs.1.2.1, ?_⟩
  intro f hf
  have hftrue : expansionLabel P P₁ f = 1 := by
    exact of_decide_eq_true (hs.2 f hf)
  by_cases h : f.val ∈ P₁
  · exact h
  · simp [expansionLabel, h] at hftrue

private theorem categorical_subdivision_of_retained (P : CollapsePair V)
    {A : PreAbstractSimplicialComplex V} (hA : A ≤ P.retained)
    {c : Vertex P.retained}
    (hc : ReflTransGen Contiguous (includeSubcomplex hA) (fun _ => c)) :
    ∃ b : Vertex (sd P.ambient), ReflTransGen Contiguous
      (includeSubcomplex (subdivision_full P.ambient A).1) (fun _ => b) := by
  let k := hA.trans P.retained_le
  let d := includeSubcomplex P.retained_le c
  have chain : ReflTransGen Contiguous (includeSubcomplex k) (fun _ => d) :=
    comp_chains id (includeSubcomplex P.retained_le) id_simplicial
      (include_subcomplex_simplicial P.retained_le) hc
  have lift := lift_chain (include_subcomplex_simplicial k)
    (constant_simplicial (K := A) d) chain
  let keep := restrictFlag P.ambient A
  have lifted := comp_chains keep id (restrictFlag_simplicial P.ambient A)
    (id_simplicial (K := sd P.ambient)) lift
  have start :
      subdivide (includeSubcomplex k) (include_subcomplex_simplicial k) ∘ keep =
        includeSubcomplex (subdivision_full P.ambient A).1 := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact face_image_include k v.val.val (keep v).val.property
  rw [Function.id_comp, Function.id_comp, start, subdivision_const] at lifted
  exact ⟨_, lifted⟩

private theorem moves_to_missing_label (P : CollapsePair V)
    {P₀ P₁ : PreAbstractSimplicialComplex V} (hP₀ : P₀ ≤ P.retained)
    (old_cover : ∀ s ∈ P.retained, s ∈ P₀ ∨ s ∈ P₁)
    (T : Finset V) (hT : T ∈ P₀) (hle : T ⊆ P.lower)
    (hfacet₁ : ∀ {j : V}, j ∈ T → oldFacet P j ∈ P₁) :
    ∃ r : Vertex (zeroRegion P P₁) → Vertex (subdivision P.ambient P₀),
      Simplicial r ∧ Contiguous
        (includeSubcomplex (show zeroRegion P P₁ ≤ sd P.ambient from fun _ hs => hs.1))
        (includeSubcomplex (subdivision_full P.ambient P₀).1 ∘ r) := by
  let U := zeroRegion P P₁
  let t : Face P.ambient := ⟨T, P.retained_le (hP₀ hT)⟩
  let f (x : Face P.ambient) := if x.val ∈ P.retained then x else t
  have subset_face {s : Finset (Face P.ambient)} (hs : s ∈ U)
      {a : Face P.ambient} (ha : a ∈ s) (new : a.val ∉ P.retained) :
      ∀ x ∈ s, t ≤ x := by
    have ha_cases : a.val = P.lower ∨ a.val = P.upper := by
      by_contra none
      exact new ((P.mem_retained_iff _).mpr
        ⟨a.property, fun e => none (Or.inl e), fun e => none (Or.inr e)⟩)
    have ha_upper : a.val ⊆ P.upper := by
      rcases ha_cases with h | h
      · rw [h]
        exact Finset.subset_insert _ _
      · rw [h]
    intro x hx
    by_cases old : x.val ∈ P.retained
    · have xle : x ≤ a := by
        by_cases e : x = a
        · exact e.le
        rcases hs.1.2.1 hx ha e with lt | lt
        · exact lt.le
        · exact (new ((P.retained.isRelLowerSet_faces old).2 lt.le
            (P.ambient.isRelLowerSet_faces a.property).1)).elim
      have not_one : x.val ∉ P₁ := by
        have hlabel : expansionLabel P P₁ x = 0 := of_decide_eq_true (hs.2 x hx)
        intro hx₁
        simp [expansionLabel, hx₁] at hlabel
      have xSub : x.val ⊆ a.val := xle
      exact missing_label_face T hfacet₁ old (xSub.trans ha_upper) not_one
    · have hx_cases : x.val = P.lower ∨ x.val = P.upper := by
        by_contra none
        exact old ((P.mem_retained_iff _).mpr
          ⟨x.property, fun e => none (Or.inl e), fun e => none (Or.inr e)⟩)
      change T ⊆ x.val
      rcases hx_cases with h | h
      · rw [h]
        exact hle
      · rw [h]
        exact hle.trans (Finset.subset_insert _ _)
  have big {s : Finset (Face P.ambient)} (hs : s ∈ U)
      (new : ∃ a ∈ s, a.val ∉ P.retained) : insert t s ∈ sd P.ambient := by
    obtain ⟨a, ha, hn⟩ := new
    have ht := subset_face hs ha hn
    refine ⟨Finset.insert_nonempty _ _, ?_, fun x _ => x.property⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hxy rfl).elim
      · exact Or.inl (lt_of_le_of_ne (ht y hy) hxy)
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inr (lt_of_le_of_ne (ht x hx) hxy.symm)
      · exact hs.1.2.1 hx hy hxy
  have f_face (s : Finset (Face P.ambient)) (hs : s ∈ U) :
      image s f ∈ subdivision P.ambient P₀ := by
    have himage (x : Face P.ambient) (hx : x ∈ image s f) : x.val ∈ P₀ := by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      by_cases h : y.val ∈ P.retained
      · have hlabel : expansionLabel P P₁ y = 0 := of_decide_eq_true (hs.2 y hy)
        have hnot : y.val ∉ P₁ := by
          intro h₁
          simp [expansionLabel, h₁] at hlabel
        simpa only [f, ite_eq_left h] using (old_cover _ h).resolve_right hnot
      · simpa only [f, ite_eq_right h] using hT
    have hchain : image s f ∈ sd P.ambient := by
      by_cases hnew : ∃ a ∈ s, a.val ∉ P.retained
      · apply (PreAbstractSimplicialComplex.isRelLowerSet_faces _ (big hs hnew)).2
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          by_cases hyold : y.val ∈ P.retained <;> simp [f, hyold, hy]
        · exact hs.1.1.image _
      · have he : image s f = s := by
          change s.image f = s
          exact (Finset.image_congr (g := id) fun a ha =>
            ite_eq_left (by_contra fun h => hnew ⟨a, ha, h⟩)).trans Finset.image_id
        rw [he]
        exact hs.1
    exact ⟨hchain.1, hchain.2.1, himage⟩
  let r := ofTotal f f_face
  refine ⟨r, of_total_simplicial f f_face, ?_⟩
  intro s hs
  have he : faceImage (includeSubcomplex (subdivision_full P.ambient P₀).1 ∘ r) hs =
      image s f := by
    change faceImage
      (ofTotal f (fun u hu => (subdivision_full P.ambient P₀).1 (f_face u hu))) hs = _
    exact ofTotal_faceImage f _ s hs
  rw [face_image_include _ s hs, he]
  by_cases hnew : ∃ a ∈ s, a.val ∉ P.retained
  · apply (PreAbstractSimplicialComplex.isRelLowerSet_faces _ (big hs hnew)).2
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_insert_of_mem h
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
        by_cases hyold : y.val ∈ P.retained <;> simp [f, hyold, hy]
    · exact hs.1.1.mono Finset.subset_union_left
  · have heq : image s f = s := by
      change s.image f = s
      exact (Finset.image_congr (g := id) fun a ha =>
        ite_eq_left (by_contra fun h => hnew ⟨a, ha, h⟩)).trans Finset.image_id
    rw [heq, Finset.union_idempotent]
    exact hs.1

/-- A two-piece categorical cover extends across a mixed elementary expansion
after two ordinary subdivisions, whenever each colour omits one old facet. -/
private theorem two_lower_sets_after_mixed_expansion (P : CollapsePair V)
    {P₀ P₁ : PreAbstractSimplicialComplex V} (hP₀ : P₀ ≤ P.retained) (hP₁ : P₁ ≤ P.retained)
    (cover : ∀ s ∈ P.retained, s ∈ P₀ ∨ s ∈ P₁)
    (categories : (∃ b : Vertex P.retained, ReflTransGen Contiguous
      (includeSubcomplex hP₀) (fun _ => b)) ∧
      (∃ b : Vertex P.retained, ReflTransGen Contiguous
      (includeSubcomplex hP₁) (fun _ => b)))
    (mixed : ∃ i ∈ P.lower, oldFacet P i ∈ P₁)
    (proper : ∃ i ∈ P.lower, oldFacet P i ∉ P₁) :
    HasCategoricalCover (NonemptyFiniteChains (Face (sd P.ambient))) 2 := by
  let T := P.lower.filter (fun i => oldFacet P i ∈ P₁)
  have hTne : T.Nonempty := by
    obtain ⟨i, hi, hi₁⟩ := mixed
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hi₁⟩⟩
  have hp : ∃ i ∈ P.lower, i ∉ T := by
    obtain ⟨i, hi, hp⟩ := proper
    exact ⟨i, hi, fun h => hp (Finset.mem_filter.mp h).2⟩
  have member₀ {i : V} (hi : i ∈ P.lower) (hiT : i ∉ T) : oldFacet P i ∈ P₀ :=
    (cover _ (oldFacet_mem_retained P hi)).resolve_right
      (fun h => hiT (Finset.mem_filter.mpr ⟨hi, h⟩))
  have hT := missing_label_mem_piece_zero T hTne (Finset.filter_subset _ _) hp member₀
  obtain ⟨r, hr, move⟩ := moves_to_missing_label P hP₀ cover T hT
    (Finset.filter_subset _ _) (fun h => (Finset.mem_filter.mp h).2)
  obtain ⟨_, old₀⟩ := categories.1
  obtain ⟨_, old₁⟩ := categories.2
  obtain ⟨b₀, cat₀⟩ := categorical_subdivision_of_retained P hP₀ old₀
  obtain ⟨b₁, cat₁⟩ := categorical_subdivision_of_retained P hP₁ old₁
  apply has_categorical_cover_of_partition (K := sd P.ambient) (expansionLabel P P₁)
  intro j
  fin_cases j
  · change ∃ b : Vertex (sd P.ambient), ReflTransGen Contiguous
      (includeSubcomplex (show zeroRegion P P₁ ≤ sd P.ambient from fun _ hs => hs.1)) (fun _ => b)
    have rest := comp_chains r id hr id_simplicial cat₀
    exact ⟨b₀, (ReflTransGen.single move).trans rest⟩
  · change ∃ b : Vertex (sd P.ambient), ReflTransGen Contiguous
      (includeSubcomplex (show oneRegion P P₁ ≤ sd P.ambient from fun _ hs => hs.1)) (fun _ => b)
    have le₁ := one_region_le_subdivision P (P₁ := P₁)
    have rest := comp_chains (includeSubcomplex le₁) id
      (include_subcomplex_simplicial le₁) id_simplicial cat₁
    exact ⟨b₁, rest⟩

private theorem retained_below_one_facet (P : CollapsePair V) {s : Finset V}
    (old : s ∈ P.retained) (hle : s ⊆ P.upper) :
    ∃ j ∈ P.lower, s ⊆ oldFacet P j := by
  have hnot : ¬ P.lower ⊆ s := old.2
  obtain ⟨j, hj, hjNot⟩ := Finset.not_subset.mp hnot
  exact ⟨j, hj, fun x hx => Finset.mem_erase.mpr ⟨fun e => hjNot (e ▸ hx), hle hx⟩⟩

private theorem categorical_zero_of_monochromatic (P : CollapsePair V)
    {A B : PreAbstractSimplicialComplex V}
    (cover : ∀ s ∈ P.retained, s ∈ A ∨ s ∈ B)
    (allB : ∀ j ∈ P.lower, oldFacet P j ∈ B)
    (b : Vertex (sd P.ambient))
    (oldChain : ReflTransGen Contiguous (includeSubcomplex (subdivision_full P.ambient A).1)
      (fun _ => b))
    (connected : ∀ u v : Vertex (sd P.ambient), (skeleton (sd P.ambient)).Reachable u v) :
    ReflTransGen Contiguous
      (includeSubcomplex (show zeroRegion P B ≤ sd P.ambient from fun _ hs => hs.1))
      (fun _ => b) := by
  let Z := zeroRegion P B
  let J := sd P.ambient
  let label (s : Face P.ambient) : Bool := decide (s.val ∈ P.retained)
  have old_limit (f : Face P.ambient) (hf : ¬ f.val ∈ P.retained) :
      f.val ⊆ P.upper := by
    by_cases he : f.val = P.lower
    · rw [he]
      exact Finset.subset_insert _ _
    have he' : f.val = P.upper := by
      by_contra ne
      exact hf ((P.mem_retained_iff _).mpr ⟨f.property, he, ne⟩)
    rw [he']
  have uniform (s : Finset (Face P.ambient)) (hs : s ∈ Z) :
      ∃ i, ∀ x ∈ s, label x = i := by
    by_cases hnew : ∃ x ∈ s, ¬ x.val ∈ P.retained
    · obtain ⟨x, hx, hn⟩ := hnew
      refine ⟨false, fun y hy => decide_eq_false ?_⟩
      intro oy
      have sub : y.val ⊆ x.val := by
        by_cases e : y = x
        · exact e.le
        rcases hs.1.2.1 hy hx e with lt | lt
        · exact lt.le
        · exact (hn ((P.retained.isRelLowerSet_faces oy).2 lt.le
            (P.ambient.isRelLowerSet_faces x.property).1)).elim
      obtain ⟨j, hj, hsub⟩ := retained_below_one_facet P oy (sub.trans (old_limit x hn))
      have hB := (B.isRelLowerSet_faces (allB j hj)).2 hsub
        (P.retained.isRelLowerSet_faces oy).1
      have hzero : expansionLabel P B y = 0 := of_decide_eq_true (hs.2 y hy)
      simp [expansionLabel] at hzero
      exact hzero hB
    · exact ⟨true, fun x hx => decide_eq_true (by
        by_contra hn
        exact hnew ⟨x, hx, hn⟩)⟩
  let part (i : Bool) := colourPiece (P := Z) label i
  have hpart (i : Bool) : part i ≤ J := fun _ hs => hs.1.1
  have oldLe : part true ≤ subdivision P.ambient A := by
    intro s hs
    refine ⟨hs.1.1.1, hs.1.1.2.1, ?_⟩
    intro x hx
    have retained : x.val ∈ P.retained := of_decide_eq_true (of_decide_eq_true (hs.2 x hx))
    have xzero : expansionLabel P B x = 0 := of_decide_eq_true (hs.1.2 x hx)
    exact (cover _ retained).resolve_right (by
      intro h
      simp [expansionLabel, h] at xzero)
  let top : Vertex J := vertexOfFace P.ambient ⟨P.upper, P.upper_mem⟩
  have collapseNew : Contiguous (includeSubcomplex (hpart false)) (fun _ => top) := by
    intro s hs
    rw [face_image_include _ s hs, constant_face_image top hs]
    refine ⟨hs.1.1.1.mono Finset.subset_union_left, ?_, fun x _ => x.property⟩
    have bounded (f : Face P.ambient) (hf : f ∈ s) : f ≤ top.val := by
      have hl : label f = false := of_decide_eq_true (hs.2 f hf)
      exact old_limit f (of_decide_eq_false hl)
    intro x hx y hy ne
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hs.1.1.2.1 hx hy ne
    · rw [Finset.mem_singleton.mp hy]
      exact Or.inl (lt_of_le_of_ne (bounded x hx) (fun e => ne (e.trans
        (Finset.mem_singleton.mp hy).symm)))
    · rw [Finset.mem_singleton.mp hx]
      exact Or.inr (lt_of_le_of_ne (bounded y hy) (fun e => ne
        ((Finset.mem_singleton.mp hx).trans e.symm)))
    · exact (ne ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm)).elim
  let starts (i : Bool) : Vertex (part i) → Vertex J := includeSubcomplex (hpart i)
  let ends (i : Bool) : Vertex (part i) → Vertex J := fun _ => b
  have branch : ∀ i, ReflTransGen Contiguous (starts i) (ends i) := by
    intro i
    cases i
    · exact (ReflTransGen.single collapseNew).trans (constant_chain_of_reachable (connected top b))
    · exact comp_chains (includeSubcomplex oldLe) id (include_subcomplex_simplicial oldLe)
        id_simplicial oldChain
  have hstart (i : Bool) : Contiguous (starts i) (starts i) := by
    intro s hs
    rw [Finset.union_idempotent]
    exact include_subcomplex_simplicial (hpart i) s hs
  have hend (i : Bool) : Contiguous (ends i) (ends i) := by
    intro s hs
    rw [Finset.union_idempotent]
    exact constant_simplicial b s hs
  exact glue_contiguity label uniform starts ends hstart hend branch

private theorem two_lower_sets_after_monochromatic_expansion (P : CollapsePair V)
    {A B : PreAbstractSimplicialComplex V}
    (hA : A ≤ P.retained) (hB : B ≤ P.retained)
    (cover : ∀ s ∈ P.retained, s ∈ A ∨ s ∈ B)
    (allB : ∀ j ∈ P.lower, oldFacet P j ∈ B)
    (cats : (∃ b : Vertex P.retained, ReflTransGen Contiguous
      (includeSubcomplex hA) (fun _ => b)) ∧
      (∃ b : Vertex P.retained, ReflTransGen Contiguous
      (includeSubcomplex hB) (fun _ => b)))
    (connected : ∀ u v : Vertex (sd P.ambient), (skeleton (sd P.ambient)).Reachable u v) :
    HasCategoricalCover (NonemptyFiniteChains (Face (sd P.ambient))) 2 := by
  obtain ⟨_, aCat⟩ := cats.1
  obtain ⟨_, bCat⟩ := cats.2
  obtain ⟨a, ha⟩ := categorical_subdivision_of_retained P hA aCat
  obtain ⟨b, hb⟩ := categorical_subdivision_of_retained P hB bCat
  apply has_categorical_cover_of_partition (K := sd P.ambient) (expansionLabel P B)
  intro j
  fin_cases j
  · exact ⟨a, categorical_zero_of_monochromatic P cover allB a ha connected⟩
  · change ∃ x : Vertex (sd P.ambient), ReflTransGen Contiguous
      (includeSubcomplex (show oneRegion P B ≤ sd P.ambient from fun _ hs => hs.1)) (fun _ => x)
    have leB := one_region_le_subdivision P (P₁ := B)
    exact ⟨b, comp_chains (includeSubcomplex leB) id
      (include_subcomplex_simplicial leB) id_simplicial hb⟩

/-- A categorical cover of the retained complex by two ordinary subcomplexes
extends across one elementary expansion after two barycentric subdivisions. -/
theorem two_lower_sets_after_elementary_expansion (P : CollapsePair V)
    (cover : CategoricalMapCover (Fin 2) (id : Vertex P.retained → Vertex P.retained))
    (connected : ∀ u v : Vertex (sd P.ambient), (skeleton (sd P.ambient)).Reachable u v) :
    HasCategoricalCover (NonemptyFiniteChains (Face (sd P.ambient))) 2 := by
  obtain ⟨C, hC, covers, cats⟩ := cover
  have hc (s : Finset V) (hs : s ∈ P.retained) : s ∈ C 0 ∨ s ∈ C 1 := by
    obtain ⟨j, hj⟩ := covers s hs
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  by_cases hAll : ∀ j ∈ P.lower, oldFacet P j ∈ C 1
  · exact two_lower_sets_after_monochromatic_expansion P (hC 0) (hC 1)
      hc hAll ⟨cats 0, cats 1⟩ connected
  by_cases hSome : ∃ j ∈ P.lower, oldFacet P j ∈ C 1
  · push_neg at hAll
    exact two_lower_sets_after_mixed_expansion P (hC 0) (hC 1) hc ⟨cats 0, cats 1⟩ hSome hAll
  · have allZero (j : V) (hj : j ∈ P.lower) : oldFacet P j ∈ C 0 :=
      (hc _ (oldFacet_mem_retained P hj)).resolve_right (fun h => hSome ⟨j, hj, h⟩)
    exact two_lower_sets_after_monochromatic_expansion P (hC 1) (hC 0)
      (fun s hs => (hc s hs).symm) allZero ⟨cats 1, cats 0⟩ connected

end
end D5.S3.Topology.StableCategory.DepthZeroElementaryExpansion
