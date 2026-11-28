/- GID: D5/S3/Topology/StableCategory/DisjointCoverObstruction
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/DisjointCoverObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One expansion forces both colours on the exterior at every ordinary depth. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import D5.S3.Topology.StableCategory.ExactCategoricalExtension

/-! A disjoint categorical vertex partition that cannot be transported across
one elementary expansion at subdivision depth one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.DisjointCoverObstruction

open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (subdivision subdivision_full)
open BarycentricBaseRigidity (Contiguous faceImage sd vertexOfFace includeVertex
  MaximalFaceCriterion baseAtDepth_le baseVertexAtDepth
  contiguity_chain_fixes_original_vertices)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial includeSubcomplex include_subcomplex_simplicial
  comp_chains)
open ExactCategoricalExtension (CategoricalIn)
open Relation (ReflTransGen)
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private categorical_of_subdivision_le from
  D5.S3.Topology.StableCategory.ExactCategoricalExtension

private def generated {X : Type} [DecidableEq X] (facets : Finset (Finset X)) :
    PreAbstractSimplicialComplex X where
  faces := {s | s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with ⟨hne, t, ht, hst⟩
    exact ⟨hne, fun u hus hu => ⟨hu, t, ht, hus.trans hst⟩⟩

private instance {X : Type} [DecidableEq X] (facets : Finset (Finset X)) (s : Finset X) :
    Decidable (s ∈ generated facets) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t))

private theorem mem_generated {X : Type} [DecidableEq X] {facets : Finset (Finset X)}
    {s : Finset X} : s ∈ generated facets ↔ s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t := Iff.rfl

private theorem generated_le {X : Type} [DecidableEq X] {facets : Finset (Finset X)}
    {J : PreAbstractSimplicialComplex X} (h : ∀ t ∈ facets, t ∈ J) :
    generated facets ≤ J := by
  intro s hs
  obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp hs
  exact (J.isRelLowerSet_faces (h t ht)).2 hst hne

private theorem image_mem_of_facets {X Y : Type} [DecidableEq X] [DecidableEq Y]
    {facets : Finset (Finset X)} {J : PreAbstractSimplicialComplex Y} (f : X → Y)
    (h : ∀ t ∈ facets, t.image f ∈ J) :
    ∀ s ∈ generated facets, s.image f ∈ J := by
  intro s hs
  obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp hs
  exact (J.isRelLowerSet_faces (h t ht)).2
    (Finset.image_subset_image hst) (hne.image f)

private abbrev Raw := Fin 6

private def gadgetFacets : Finset (Finset Raw) :=
  {{0, 1, 5}, {0, 2, 3}, {0, 3, 5}, {1, 4, 5}, {2, 3, 4}, {3, 4, 5}}

private def cycleEdges : Finset (Finset Raw) := {{1, 4}, {2, 4}, {1, 2}}

private def cycleFaces : Finset (Finset Raw) :=
  {{1}, {2}, {4}, {1, 4}, {2, 4}, {1, 2}}

private abbrev C := generated cycleEdges
private abbrev P := generated (insert {0, 1, 2} gadgetFacets)

private theorem cycle_le : C ≤ P :=
  generated_le (by decide +kernel)

private theorem cycle_face_table :
    ∀ s ∈ (Finset.univ : Finset Raw).powerset, s ∈ C → s ∈ cycleFaces := by
  decide +kernel

private theorem in_cycle_table {s : Finset Raw} (hs : s ∈ C) : s ∈ cycleFaces :=
  cycle_face_table s (Finset.mem_powerset.mpr (Finset.subset_univ _)) hs

private theorem cycle_edge_max_table :
    ∀ e ∈ cycleEdges, ∀ t ∈ cycleEdges, e ⊆ t → t ⊆ e := by
  decide +kernel

private theorem cycle_edge_max (e : Finset Raw) (he : e ∈ cycleEdges) :
    ∃ F : Face C, F.val = e ∧ IsMax F := by
  have heC : ∀ t ∈ cycleEdges, t ∈ C := by decide +kernel
  let F : Face C := ⟨e, heC e he⟩
  refine ⟨F, rfl, ?_⟩
  intro U hFU
  obtain ⟨_, t, ht, hUt⟩ := mem_generated.mp U.property
  have heU : e ⊆ U.val := hFU
  exact hUt.trans (cycle_edge_max_table e he t ht (heU.trans hUt))

private theorem criterion_table :
    ∀ a : Raw, ∀ w : Raw, ({a} : Finset Raw) ∈ C →
      (∀ e ∈ cycleEdges, a ∈ e → insert w e ∈ P) → w = a := by
  decide +kernel

private theorem cycle_criterion : MaximalFaceCriterion P C := by
  intro a w h
  apply criterion_table a.val w a.property
  intro e he ha
  obtain ⟨F, rfl, hF⟩ := cycle_edge_max e he
  have eq : @insert Raw (Finset Raw) (@Finset.instInsert Raw (Classical.decEq Raw))
      w F.val = insert w F.val := by
    ext x
    simp only [Finset.mem_insert]
  rw [← eq]
  exact h F hF ha

private def replaceMidpoint (s : Finset Raw) : Finset Raw :=
  if s = {1, 4} then {1, 4, 5}
  else if s = {2, 4} then {2, 3, 4}
  else if s = {1, 2} then {0, 1, 2}
  else s

private theorem replacement_mem :
    ∀ s ∈ cycleFaces, replaceMidpoint s ∈ P := by
  decide +kernel

private theorem replacement_comparable :
    ∀ s ∈ cycleFaces, ∀ t ∈ cycleFaces, (s ⊆ t ∨ t ⊆ s) →
      (s ⊆ replaceMidpoint t ∨ replaceMidpoint t ⊆ s) ∧
      (replaceMidpoint s ⊆ replaceMidpoint t ∨ replaceMidpoint t ⊆ replaceMidpoint s) := by
  decide +kernel

private abbrev Source := subdivision P C

private noncomputable def replaced (v : Vertex Source) : Vertex (sd P) :=
  vertexOfFace P ⟨replaceMidpoint v.val.val,
    replacement_mem _ (in_cycle_table (v.property.2.2 _ (Finset.mem_singleton_self _)))⟩

private theorem pairs_comparable {Y : Type} {J : PreAbstractSimplicialComplex Y}
    {s : Finset (Face J)} (hs : IsChain (· < ·) (s : Set (Face J))) {a b : Face J}
    (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a := by
  by_cases h : a = b
  · exact Or.inl h.le
  · exact (hs ha hb h).imp le_of_lt le_of_lt

noncomputable section

local instance (priority := 2000) (X : Type) : DecidableEq X := Classical.decEq X

private theorem flag_union_of_comparable {X Y : Type}
    {U : PreAbstractSimplicialComplex X} {J : PreAbstractSimplicialComplex Y}
    {s : Finset X} (hs : s ∈ U) (f g : Vertex U → Vertex (sd J))
    (h : ∀ x y : Vertex U, x.val ∈ s → y.val ∈ s →
      ∀ a b : Face J, (a = (f x).val ∨ a = (g x).val) →
      (b = (f y).val ∨ b = (g y).val) → a ≤ b ∨ b ≤ a) :
    faceImage f hs ∪ faceImage g hs ∈ sd J := by
  classical
  have hmem (a : Face J) (ha : a ∈ faceImage f hs ∪ faceImage g hs) :
      ∃ x : Vertex U, x.val ∈ s ∧ (a = (f x).val ∨ a = (g x).val) := by
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff f hs a).mp ha
      exact ⟨x, hx, Or.inl rfl⟩
    · obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff g hs a).mp ha
      exact ⟨x, hx, Or.inr rfl⟩
  refine ⟨((U.isRelLowerSet_faces hs).1.attach.image _).mono
    Finset.subset_union_left, ?_, fun a _ => a.property⟩
  intro a ha b hb hab
  obtain ⟨x, hx, hxa⟩ := hmem a ha
  obtain ⟨y, hy, hyb⟩ := hmem b hb
  exact (h x y hx hy a b hxa hyb).imp
    (fun hle => lt_of_le_of_ne hle hab) (fun hle => lt_of_le_of_ne hle hab.symm)

end

private theorem inclusion_contiguous_replaced :
    Contiguous (includeVertex (baseAtDepth_le cycle_le 1)) replaced := by
  intro s hs
  apply flag_union_of_comparable hs
  intro x y hx hy a b ha hb
  have hxy := pairs_comparable hs.2.1 hx hy
  have hm := replacement_comparable x.val.val (in_cycle_table (hs.2.2 _ hx))
    y.val.val (in_cycle_table (hs.2.2 _ hy)) hxy
  have hm' := replacement_comparable y.val.val (in_cycle_table (hs.2.2 _ hy))
    x.val.val (in_cycle_table (hs.2.2 _ hx)) (hxy.elim Or.inr Or.inl)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hxy
  · exact hm.1
  · exact hm'.1.elim Or.inr Or.inl
  · exact hm.2

/-- The six vertices run through the singletons 1, 4, 2 and the triangle
barycenters 145, 234, 012. Their map from the subdivided raw cycle has
no finite contiguity chain to a constant in the subdivision of P. -/
theorem replaced_cycle_noncategorical (b : Vertex (sd P)) :
    ¬ ReflTransGen Contiguous replaced (fun _ => b) := by
  intro h
  have h' := (ReflTransGen.single inclusion_contiguous_replaced).trans h
  let a₁ : Vertex C := ⟨1, by decide +kernel⟩
  let a₂ : Vertex C := ⟨2, by decide +kernel⟩
  have h₁ := contiguity_chain_fixes_original_vertices cycle_le cycle_criterion 1 h' a₁
  have h₂ := contiguity_chain_fixes_original_vertices cycle_le cycle_criterion 1 h' a₂
  have he := congrArg (fun v : Vertex (sd P) => v.val.val) (h₁.symm.trans h₂)
  change ({1} : Finset Raw) = {2} at he
  exact (by decide +kernel : ({1} : Finset Raw) ≠ {2}) he


abbrev Labels := Fin 11

private def copyVertex (i : Bool) (x : Raw) : Labels :=
  if i && decide (x ≠ 0) then ⟨x.val + 5, by have := x.isLt; omega⟩
  else ⟨x.val, by have := x.isLt; omega⟩

private def copyFacets (i : Bool) : Finset (Finset Labels) :=
  gadgetFacets.image fun s => s.image (copyVertex i)

def chamber : Finset Labels := {0, 1, 2, 6, 7}

def freeFacet : Finset Labels := {1, 2, 6, 7}

private def hornFacets : Finset (Finset Labels) :=
  freeFacet.image fun x => chamber.erase x

private def oldFacets : Finset (Finset Labels) :=
  copyFacets false ∪ copyFacets true ∪ hornFacets

private def newFacets : Finset (Finset Labels) :=
  insert chamber (copyFacets false ∪ copyFacets true)

private def pieceFacets (i : Bool) : Finset (Finset Labels) :=
  copyFacets i ∪ ({copyVertex i 1, copyVertex i 2} : Finset Labels).image
    (fun x => chamber.erase x)

def Old : PreAbstractSimplicialComplex Labels := generated oldFacets
def New : PreAbstractSimplicialComplex Labels := generated newFacets
private abbrev D (i : Bool) := generated (pieceFacets i)

private instance (s : Finset Labels) : Decidable (s ∈ Old) :=
  inferInstanceAs (Decidable (s ∈ generated oldFacets))

private instance (s : Finset Labels) : Decidable (s ∈ New) :=
  inferInstanceAs (Decidable (s ∈ generated newFacets))

theorem old_le_new : Old ≤ New :=
  generated_le (by decide +kernel)

private theorem chamber_mem : chamber ∈ New := by decide +kernel

private theorem expansion_table :
    ∀ t ∈ newFacets, ∀ s ∈ t.powerset, s.Nonempty →
      s ∉ Old → s = freeFacet ∨ s = chamber := by
  decide +kernel

/-- The attached simplex has five vertices, and the only new faces are
the chamber and its free facet opposite vertex 0. -/
theorem elementary_expansion_faces (s : Finset Labels) :
    (s ∈ New ∧ s ∉ Old) ↔ s = freeFacet ∨ s = chamber := by
  constructor
  · rintro ⟨hs, hold⟩
    obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp hs
    exact expansion_table t ht s (Finset.mem_powerset.mpr hst) hne hold
  · rintro (rfl | rfl) <;> decide +kernel

theorem free_facet_cofaces :
    freeFacet = chamber.erase 0 ∧
      ∀ s ∈ New, freeFacet ⊆ s → s = freeFacet ∨ s = chamber := by
  refine ⟨by decide +kernel, ?_⟩
  intro s hs hsub
  have hfree : freeFacet ∉ Old := by decide +kernel
  have hne : freeFacet.Nonempty := by decide +kernel
  exact (elementary_expansion_faces s).mp
    ⟨hs, fun h => hfree ((Old.isRelLowerSet_faces h).2 hsub hne)⟩

theorem dimension_four :
    chamber ∈ New ∧ chamber.card = 5 ∧ ∀ s ∈ New, s.card ≤ 5 := by
  have hcard : ∀ t ∈ newFacets, t.card ≤ 5 := by decide +kernel
  refine ⟨chamber_mem, by decide +kernel, ?_⟩
  intro s hs
  obtain ⟨_, t, ht, hst⟩ := mem_generated.mp hs
  exact (Finset.card_le_card hst).trans (hcard t ht)

private theorem piece_facets_old :
    ∀ i : Bool, ∀ t ∈ pieceFacets i, t ∈ Old := by
  decide +kernel

private theorem piece_le_old (i : Bool) : D i ≤ Old :=
  generated_le (piece_facets_old i)

private def foldVertex (i : Bool) (src dst : Raw) (x : Labels) : Labels :=
  if x = copyVertex i src then copyVertex i dst else x

private def foldOtherLeaves (i : Bool) (x : Labels) : Labels :=
  if x = copyVertex (!i) 1 ∨ x = copyVertex (!i) 2 then 0 else x

/-- The six contiguous moves, with each row expressed on the original vertices. -/
private def foldRow (i : Bool) (j : Fin 7) (x : Labels) : Labels :=
  let r₁ := foldOtherLeaves i x
  let r₂ := foldVertex i 1 5 r₁
  let r₃ := foldVertex i 0 3 r₂
  let r₄ := foldVertex i 2 3 r₃
  let r₅ := foldVertex i 3 4 r₄
  let r₆ := foldVertex i 4 5 r₅
  if j = 0 then x else if j = 1 then r₁ else if j = 2 then r₂
  else if j = 3 then r₃ else if j = 4 then r₄ else if j = 5 then r₅ else r₆

private theorem fold_row_table :
    ∀ i : Bool, ∀ j : Fin 7, ∀ t ∈ pieceFacets i, t.image (foldRow i j) ∈ D i := by
  decide +kernel

private theorem fold_step_table :
    ∀ i : Bool, ∀ j : Fin 6, ∀ t ∈ pieceFacets i,
      t.image (foldRow i j.castSucc) ∪ t.image (foldRow i j.succ) ∈ D i := by
  decide +kernel

private theorem fold_end_table :
    ∀ i : Bool, ∀ x : Labels, ({x} : Finset Labels) ∈ D i →
      foldRow i 6 x = copyVertex i 5 := by
  decide +kernel

private def row (i : Bool) (j : Fin 7) (v : Vertex (D i)) : Vertex (D i) :=
  ⟨foldRow i j v.val, by
    simpa only [Finset.image_singleton] using
      image_mem_of_facets (foldRow i j) (fold_row_table i j) _ v.property⟩

private theorem contiguous_of_containing_face {X Y : Type}
    {U : PreAbstractSimplicialComplex X} {J : PreAbstractSimplicialComplex Y}
    {f g : Vertex U → Vertex J}
    (h : ∀ s, s ∈ U → ∃ t ∈ J, ∀ v : Vertex U, v.val ∈ s →
      (f v).val ∈ t ∧ (g v).val ∈ t) : Contiguous f g := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := h s hs
  apply (J.isRelLowerSet_faces ht).2
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff f hs y).mp hy
      exact (hst v hv).1
    · obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff g hs y).mp hy
      exact (hst v hv).2
  · exact ((U.isRelLowerSet_faces hs).1.attach.image _).mono Finset.subset_union_left

private theorem row_step (i : Bool) (j : Fin 6) :
    Contiguous (row i j.castSucc) (row i j.succ) := by
  apply contiguous_of_containing_face
  intro s hs
  obtain ⟨_, t, ht, hst⟩ := mem_generated.mp hs
  refine ⟨_, fold_step_table i j t ht, ?_⟩
  intro v hv
  exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hst hv)),
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hst hv))⟩

private theorem id_simplicial {X : Type} (J : PreAbstractSimplicialComplex X) :
    Simplicial (id : Vertex J → Vertex J) :=
  include_subcomplex_simplicial (le_refl J)

private theorem piece_categorical (i : Bool) : CategoricalIn (piece_le_old i) := by
  have h : ReflTransGen Contiguous (row i 0) (row i 6) :=
    ((((((ReflTransGen.single (row_step i 0)).tail (row_step i 1)).tail
      (row_step i 2)).tail (row_step i 3)).tail (row_step i 4)).tail (row_step i 5))
  let b : Vertex (D i) := ⟨copyVertex i 5, by
    have hvertex : ∀ j : Bool, ({copyVertex j 5} : Finset Labels) ∈ D j := by
      decide +kernel
    exact hvertex i⟩
  have hstart : row i 0 = id := by
    funext v
    apply Subtype.ext
    rfl
  have hend : row i 6 = fun _ => b := by
    funext v
    exact Subtype.ext (fold_end_table i v.val v.property)
  rw [hstart, hend] at h
  refine ⟨includeSubcomplex (piece_le_old i) b, ?_⟩
  exact comp_chains id (includeSubcomplex (piece_le_old i)) (id_simplicial (D i))
    (include_subcomplex_simplicial (piece_le_old i)) h

private def oldColourRaw (s : Finset Labels) : Bool :=
  if s ∈ generated (copyFacets false) then false
  else if s ∈ generated (copyFacets true) then true
  else decide (s ∉ D false)

def oldColour (a : Face Old) : Bool := oldColourRaw a.val

def region {X : Type} (J : PreAbstractSimplicialComplex X)
    (paint : Face J → Bool) (i : Bool) : PreAbstractSimplicialComplex (Face J) :=
  colourComplex (sd J) fun a => decide (paint a = i)

theorem region_le {X : Type} (J : PreAbstractSimplicialComplex X)
    (paint : Face J → Bool) (i : Bool) : region J paint i ≤ sd J :=
  fun _ hs => hs.1

private theorem colour_membership_table :
    ∀ t ∈ oldFacets, ∀ s ∈ t.powerset, s.Nonempty → s ∈ D (oldColourRaw s) := by
  decide +kernel

private theorem old_region_le (i : Bool) : region Old oldColour i ≤ subdivision Old (D i) := by
  intro s hs
  refine ⟨hs.1.1, hs.1.2.1, ?_⟩
  intro a ha
  have hc : oldColourRaw a.val = i := of_decide_eq_true (hs.2 a ha)
  obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp a.property
  rw [← hc]
  exact colour_membership_table t ht a.val (Finset.mem_powerset.mpr hst) hne

theorem old_regions_categorical (i : Bool) : CategoricalIn (region_le Old oldColour i) :=
  categorical_of_subdivision_le (old_region_le i) (piece_le_old i) (piece_categorical i)

private def retractVertex (i : Bool) (x : Labels) : Raw :=
  if i then
    if h : 5 < x.val then ⟨x.val - 5, by have := x.isLt; omega⟩ else 0
  else
    if h : x.val < 6 then ⟨x.val, h⟩ else 0

private theorem retract_facet_table :
    ∀ i : Bool, ∀ t ∈ newFacets, t.image (retractVertex i) ∈ P := by
  decide +kernel

private noncomputable def retract (i : Bool) (v : Vertex (sd New)) : Vertex (sd P) :=
  vertexOfFace P ⟨v.val.val.image (retractVertex i),
    image_mem_of_facets (retractVertex i) (retract_facet_table i) _ v.val.property⟩

private theorem simplicial_of_flag_comparison {X Y : Type}
    {U : PreAbstractSimplicialComplex X} {J : PreAbstractSimplicialComplex Y}
    (f : Vertex U → Vertex (sd J))
    (h : ∀ s, s ∈ U → ∀ x y : Vertex U, x.val ∈ s → y.val ∈ s →
      (f x).val ≤ (f y).val ∨ (f y).val ≤ (f x).val) : Simplicial f := by
  classical
  intro s hs
  have hu := flag_union_of_comparable hs f f (by
    intro x y hx hy a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact h s hs x y hx hy)
  simpa only [Finset.union_idempotent] using hu

private theorem retract_simplicial (i : Bool) : Simplicial (retract i) := by
  apply simplicial_of_flag_comparison
  intro s hs x y hx hy
  exact (pairs_comparable hs.2.1 hx hy).imp
    Finset.image_subset_image Finset.image_subset_image

def chamberBarycenter : Face New := ⟨chamber, chamber_mem⟩

private def witnessRaw (i : Bool) (s : Finset Raw) : Finset Labels :=
  if s = {1, 2} then chamber else (replaceMidpoint s).image (copyVertex i)

private theorem witness_mem_table :
    ∀ i : Bool, ∀ s ∈ cycleFaces, witnessRaw i s ∈ New := by
  decide +kernel

private theorem witness_colour_table :
    ∀ i : Bool, ∀ s ∈ cycleFaces, s ≠ {1, 2} →
      witnessRaw i s ∈ Old ∧ oldColourRaw (witnessRaw i s) = i := by
  decide +kernel

private theorem witness_comparison_table :
    ∀ i : Bool, ∀ s ∈ cycleFaces, ∀ t ∈ cycleFaces, (s ⊆ t ∨ t ⊆ s) →
      (witnessRaw i s ⊆ witnessRaw i t ∨ witnessRaw i t ⊆ witnessRaw i s) := by
  decide +kernel

private theorem witness_retract_table :
    ∀ i : Bool, ∀ s ∈ cycleFaces,
      (witnessRaw i s).image (retractVertex i) = replaceMidpoint s := by
  decide +kernel

/-- Equality of labels on old face vertices is exact retention of the disjoint
vertex partition. -/
def Retains (paint : Face New → Bool) : Prop :=
  ∀ a : Face Old, paint ⟨a.val, old_le_new a.property⟩ = oldColour a

private theorem source_vertex_mem (v : Vertex Source) : v.val.val ∈ cycleFaces :=
  in_cycle_table (v.property.2.2 _ (Finset.mem_singleton_self _))

private def witnessFace (i : Bool) (v : Vertex Source) : Face New :=
  ⟨witnessRaw i v.val.val, witness_mem_table i _ (source_vertex_mem v)⟩

private theorem witness_colour (paint : Face New → Bool) (hpaint : Retains paint)
    (v : Vertex Source) : paint (witnessFace (paint chamberBarycenter) v) =
      paint chamberBarycenter := by
  let i := paint chamberBarycenter
  change paint (witnessFace i v) = i
  by_cases he : v.val.val = ({1, 2} : Finset Raw)
  · have hv : witnessFace i v = chamberBarycenter := by
      apply Subtype.ext
      change witnessRaw i v.val.val = chamber
      simp [witnessRaw, he]
    rw [hv]
  · obtain ⟨hold, hc⟩ := witness_colour_table i _ (source_vertex_mem v) he
    let a : Face Old := ⟨witnessRaw i v.val.val, hold⟩
    exact (hpaint a).trans hc

private def witness (paint : Face New → Bool) (hpaint : Retains paint)
    (v : Vertex Source) : Vertex (region New paint (paint chamberBarycenter)) :=
  ⟨witnessFace (paint chamberBarycenter) v, (vertexOfFace New _).property, by
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact decide_eq_true (witness_colour paint hpaint v)⟩

private theorem witness_simplicial (paint : Face New → Bool) (hpaint : Retains paint) :
    Simplicial (witness paint hpaint) := by
  let i := paint chamberBarycenter
  let f : Vertex Source → Vertex (sd New) :=
    includeSubcomplex (region_le New paint i) ∘ witness paint hpaint
  have hf : Simplicial f := by
    apply simplicial_of_flag_comparison
    intro s hs x y hx hy
    exact witness_comparison_table i _ (source_vertex_mem x) _ (source_vertex_mem y)
      (pairs_comparable hs.2.1 hx hy)
  intro s hs
  refine ⟨hf s hs, ?_⟩
  intro a ha
  obtain ⟨v, _, rfl⟩ := (mem_faceImage_iff (witness paint hpaint) hs a).mp ha
  exact decide_eq_true (witness_colour paint hpaint v)

/-- The region that receives the chamber barycenter cannot be categorical.
This is independent of the colour assigned to the new free-facet barycenter. -/
theorem chamber_colour_noncategorical (paint : Face New → Bool) (hpaint : Retains paint) :
    ¬ CategoricalIn (region_le New paint (paint chamberBarycenter)) := by
  rintro ⟨b, hb⟩
  let i := paint chamberBarycenter
  have hchain := comp_chains (witness paint hpaint) (retract i)
    (witness_simplicial paint hpaint) (retract_simplicial i) hb
  have hstart : retract i ∘ includeSubcomplex (region_le New paint i) ∘ witness paint hpaint =
      replaced := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact witness_retract_table i _ (source_vertex_mem v)
  rw [hstart] at hchain
  exact replaced_cycle_noncategorical (retract i b) hchain

/-- A disjoint vertex partition of the old subdivision has two categorical
induced regions, but every retention of the partition fails categoricality. -/
theorem disjoint_partition_obstruction :
    (∀ i : Bool, CategoricalIn (region_le Old oldColour i)) ∧
      ¬ ∃ paint : Face New → Bool, Retains paint ∧
        ∀ i : Bool, CategoricalIn (region_le New paint i) := by
  refine ⟨old_regions_categorical, ?_⟩
  rintro ⟨paint, hpaint, hcat⟩
  exact chamber_colour_noncategorical paint hpaint (hcat (paint chamberBarycenter))


open BarycentricNeighborhoodIteration (FullIn iteratedAmbient iteratedSubcomplex)
open BarycentricBaseRigidity (baseAtDepth subdividedVertex retainedVertex)
open GraphSubdivisionIntervals (mem_iteratedSubcomplex_iff)
open OrdinaryContiguityLift (subdivide lift_chain)
open private iterated_le singleton_subdivision from D5.S3.Topology.BarycentricBaseRigidity
open private restrictFlag restrictFlag_simplicial face_image_include face_image_comp
  subdivision_comp finite_at_depth from D5.S3.Topology.StableCategory.FourPieceCategoricalCover
open private subdivide_simplicial from D5.S3.Topology.StableCategory.TerminalCarrierIteration

theorem region_at_le (paint : Face New → Bool) (i : Bool) (n : ℕ) :
    iteratedSubcomplex (sd New) (region New paint i) n ≤ (iteratedAmbient (sd New) n).2 :=
  iterated_le (region_le New paint i) n

/-- Subdivide a map between subcomplexes using the face carriers of their
respective ambient complexes. -/
private noncomputable def subdivideInto {X Y : Type}
    {K A : PreAbstractSimplicialComplex X} {L B : PreAbstractSimplicialComplex Y}
    (hB : B ≤ L) (f : Vertex A → Vertex B) (hf : Simplicial f)
    (v : Vertex (subdivision K A)) : Vertex (subdivision L B) :=
  let a := (restrictFlag K A v).val
  ⟨⟨faceImage f a.property, hB (hf a.val a.property)⟩,
    singleton_subdivision.mpr (hf a.val a.property)⟩

private theorem subdivide_into_factors {X Y : Type}
    {K A : PreAbstractSimplicialComplex X} {L B : PreAbstractSimplicialComplex Y}
    (hB : B ≤ L) (f : Vertex A → Vertex B) (hf : Simplicial f) :
    subdivide (includeSubcomplex hB ∘ f) ((include_subcomplex_simplicial hB).comp hf) ∘
        restrictFlag K A =
      includeSubcomplex (subdivision_full L B).1 ∘ subdivideInto (K := K) hB f hf := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  let a := (restrictFlag K A v).val
  exact (face_image_comp f (includeSubcomplex hB) a.val a.property (hf a.val a.property)).trans
    (face_image_include hB _ _)

private theorem subdivide_into_simplicial {X Y : Type}
    {K A : PreAbstractSimplicialComplex X} {L B : PreAbstractSimplicialComplex Y}
    (hB : B ≤ L) (f : Vertex A → Vertex B) (hf : Simplicial f) :
    Simplicial (subdivideInto (K := K) hB f hf) := by
  let g := subdivideInto (K := K) hB f hf
  have hg : Simplicial (includeSubcomplex (subdivision_full L B).1 ∘ g) := by
    change Simplicial (includeSubcomplex (subdivision_full L B).1 ∘
      subdivideInto (K := K) hB f hf)
    rw [← subdivide_into_factors]
    exact (subdivide_simplicial _ _).comp (restrictFlag_simplicial K A)
  intro s hs
  have hmem : faceImage g hs ∈ sd L := hg s hs
  refine ⟨hmem.1, hmem.2.1, ?_⟩
  intro b hb
  obtain ⟨v, _, rfl⟩ := (mem_faceImage_iff g hs b).mp hb
  exact (g v).property.2.2 _ (Finset.mem_singleton_self _)

private theorem witness_comparison_at (paint : Face New → Bool) (hpaint : Retains paint) (n : ℕ) :
    ∃ f : Vertex (baseAtDepth P C (n + 1)) →
        Vertex (iteratedSubcomplex (sd New) (region New paint (paint chamberBarycenter)) n),
      ∃ r : Vertex (iteratedAmbient (sd New) n).2 → Vertex (iteratedAmbient (sd P) n).2,
        Simplicial f ∧ Simplicial r ∧ ReflTransGen Contiguous
          (includeSubcomplex (baseAtDepth_le cycle_le (n + 1)))
          (r ∘ includeSubcomplex (region_at_le paint (paint chamberBarycenter) n) ∘ f) := by
  let i := paint chamberBarycenter
  induction n with
  | zero =>
    refine ⟨witness paint hpaint, retract i, witness_simplicial paint hpaint,
      retract_simplicial i, ?_⟩
    have he : retract i ∘ includeSubcomplex (region_le New paint i) ∘ witness paint hpaint =
        replaced := by
      funext v
      apply Subtype.ext
      apply Subtype.ext
      exact witness_retract_table i _ (source_vertex_mem v)
    change ReflTransGen Contiguous (includeVertex (baseAtDepth_le cycle_le 1))
      (retract i ∘ includeSubcomplex (region_le New paint i) ∘ witness paint hpaint)
    rw [he]
    exact .single inclusion_contiguous_replaced
  | succ n ih =>
    obtain ⟨f, r, hf, hr, chain⟩ := ih
    let K := (iteratedAmbient (sd P) n).2
    let A := baseAtDepth P C (n + 1)
    let L := (iteratedAmbient (sd New) n).2
    let B := iteratedSubcomplex (sd New) (region New paint i) n
    let hA : A ≤ K := baseAtDepth_le cycle_le (n + 1)
    let hB : B ≤ L := region_at_le paint i n
    let pre := restrictFlag K A
    let fAmbient := includeSubcomplex hB ∘ f
    have hfAmbient : Simplicial fAmbient := (include_subcomplex_simplicial hB).comp hf
    have hinc := include_subcomplex_simplicial hA
    let : Finite (BarycentricBaseRigidity.ambientAtDepth P (n + 1)).1 :=
      finite_at_depth (sd P) n
    have hlift := lift_chain hinc (hr.comp hfAmbient) chain
    have hcomp := comp_chains pre id (restrictFlag_simplicial K A) (id_simplicial (sd K)) hlift
    have hstart : subdivide (includeSubcomplex hA) hinc ∘ pre =
        includeSubcomplex (subdivision_full K A).1 := by
      funext v
      apply Subtype.ext
      apply Subtype.ext
      exact face_image_include hA v.val.val (pre v).val.property
    have hend : subdivide (r ∘ fAmbient) (hr.comp hfAmbient) ∘ pre =
        subdivide r hr ∘ includeSubcomplex (subdivision_full L B).1 ∘
          subdivideInto (K := K) hB f hf := by
      rw [subdivision_comp fAmbient r hfAmbient hr]
      funext v
      exact congrArg (subdivide r hr) (congrFun (subdivide_into_factors (K := K) hB f hf) v)
    simp only [Function.id_comp] at hcomp
    rw [hstart, hend] at hcomp
    exact ⟨subdivideInto (K := K) hB f hf, subdivide r hr,
      subdivide_into_simplicial hB f hf, subdivide_simplicial r hr, hcomp⟩

private theorem retained_vertex_injective {X : Type} {J : PreAbstractSimplicialComplex X} (n : ℕ) :
    Function.Injective (retainedVertex (J := J) n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    intro a b h
    apply ih
    apply Subtype.ext
    apply Finset.singleton_injective
    exact congrArg (fun v : Vertex (iteratedAmbient J (n + 1)).2 => v.val.val) h

/-- The chamber's colour region remains noncategorical after every further
common subdivision, for any colouring retaining the old partition. -/
theorem chamber_colour_noncategorical_at (paint : Face New → Bool) (hpaint : Retains paint)
    (n : ℕ) : ¬ CategoricalIn (region_at_le paint (paint chamberBarycenter) n) := by
  rintro ⟨b, hb⟩
  obtain ⟨f, r, hf, hr, hc⟩ := witness_comparison_at paint hpaint n
  have chain : ReflTransGen Contiguous (includeVertex (baseAtDepth_le cycle_le (n + 1)))
      (fun _ => r b) := hc.trans (comp_chains f r hf hr hb)
  let a₁ : Vertex C := ⟨1, by decide +kernel⟩
  let a₂ : Vertex C := ⟨2, by decide +kernel⟩
  have h₁ := contiguity_chain_fixes_original_vertices cycle_le cycle_criterion (n + 1) chain a₁
  have h₂ := contiguity_chain_fixes_original_vertices cycle_le cycle_criterion (n + 1) chain a₂
  have he : retainedVertex n (subdividedVertex (includeVertex cycle_le a₁)) =
      retainedVertex n (subdividedVertex (includeVertex cycle_le a₂)) := h₁.symm.trans h₂
  have hne := congrArg (fun v : Vertex (sd P) => v.val.val) (retained_vertex_injective n he)
  change ({1} : Finset Raw) = {2} at hne
  exact (by decide +kernel : ({1} : Finset Raw) ≠ {2}) hne

/-- Keep the old face colours and give every new face colour `i`. -/
noncomputable def monochromePaint (i : Bool) (a : Face New) : Bool := by
  classical
  exact if h : a.val ∈ Old then oldColour ⟨a.val, h⟩ else i

theorem monochromePaint_retains (i : Bool) : Retains (monochromePaint i) := by
  intro a
  simp [monochromePaint, a.property]

theorem monochromePaint_exterior (i : Bool) (a : Face New) (ha : a.val ∉ Old) :
    monochromePaint i a = i := by
  simp [monochromePaint, ha]

/-- Assigning the whole exterior to one colour produces a noncategorical
region at every ordinary depth `n + 1`. -/
theorem monochrome_exterior_noncategorical (i : Bool) (n : ℕ) :
    ¬ CategoricalIn (region_at_le (monochromePaint i) i n) := by
  have hi := monochromePaint_exterior i chamberBarycenter
    ((elementary_expansion_faces chamber).mpr (Or.inr rfl)).2
  simpa only [hi] using chamber_colour_noncategorical_at (monochromePaint i)
    (monochromePaint_retains i) n

/-- A full piece containing its inherited colour region and every exterior
vertex at depth `n + 1` is noncategorical, allowing overlap with another piece. -/
theorem full_piece_with_exterior_noncategorical (i : Bool) (n : ℕ)
    {Q : PreAbstractSimplicialComplex (iteratedAmbient (sd New) n).1}
    (hQ : FullIn Q (iteratedAmbient (sd New) n).2)
    (hOld : iteratedSubcomplex (sd New)
      (subdivision New Old ⊓ region New (monochromePaint i) i) n ≤ Q)
    (hExterior : ∀ v : Vertex (iteratedAmbient (sd New) n).2,
      {v.val} ∉ iteratedSubcomplex (sd New) (subdivision New Old) n → {v.val} ∈ Q) :
    ¬ CategoricalIn hQ.1 := by
  let paint := monochromePaint i
  let R := iteratedSubcomplex (sd New) (region New paint i) n
  have hRQ : R ≤ Q := by
    intro s hs
    apply hQ.2 ⟨s, region_at_le paint i n hs⟩
    intro v hv
    have hvR : {v} ∈ R := (R.isRelLowerSet_faces hs).2
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hvA := region_at_le paint i n hvR
    by_cases hvO : {v} ∈ iteratedSubcomplex (sd New) (subdivision New Old) n
    · exact hOld ((mem_iteratedSubcomplex_iff n hvA).mpr
        ⟨(mem_iteratedSubcomplex_iff (B := subdivision New Old) n hvA).mp hvO,
          (mem_iteratedSubcomplex_iff (B := region New paint i) n hvA).mp hvR⟩)
    · exact hExterior ⟨v, hvA⟩ hvO
  rintro ⟨b, hb⟩
  exact monochrome_exterior_noncategorical i n
    ⟨b, comp_chains (includeSubcomplex hRQ) id (include_subcomplex_simplicial hRQ)
      (id_simplicial (iteratedAmbient (sd New) n).2) hb⟩

end D5.S3.Topology.StableCategory.DisjointCoverObstruction
