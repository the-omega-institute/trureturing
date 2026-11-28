/- GID: D5/S3/Topology/StableCategory/ProductRigidCores
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ProductRigidCores
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original product of the seven-triangle face poset has category three. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import D5.S3.Topology.BarycentricGraphDistance
import D5.S3.Topology.ConnectedCategoryGraft

/-!
# Ordinary finite-space category of the seven-triangle product

The two-ball is the boundary of an octahedron with the triangle 124 removed.
The three exceptional triangles along that boundary give the product obstruction.
-/

set_option autoImplicit false

namespace D5.S3.Topology.ProductRigidCores

open BarycentricGraphDistance (Face)
open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open Relation (EqvGen)

abbrev VertexLabel := Fin 6

private def generated (facets : Finset (Finset VertexLabel)) :
    PreAbstractSimplicialComplex VertexLabel where
  faces := {s | s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    change s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t at hs
    obtain ⟨hne, t, ht, hst⟩ := hs
    exact ⟨hne, fun u hus hu => ⟨hu, t, ht, hus.trans hst⟩⟩

private instance (facets : Finset (Finset VertexLabel)) (s : Finset VertexLabel) :
    Decidable (s ∈ generated facets) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t))

private theorem mem_generated {facets : Finset (Finset VertexLabel)} {s : Finset VertexLabel} :
    s ∈ generated facets ↔ s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t :=
  Iff.rfl

def facets : Finset (Finset VertexLabel) :=
  {{0, 1, 2}, {0, 1, 5}, {0, 2, 3}, {0, 3, 5}, {1, 4, 5}, {2, 3, 4}, {3, 4, 5}}

abbrev P : PreAbstractSimplicialComplex VertexLabel := generated facets

abbrev Factor := Face P
abbrev ProductPoset := Factor × Factor

private def cornerRaw : Fin 3 → Finset VertexLabel := ![{4}, {2}, {1}]
private def edgeRaw : Fin 3 → Finset VertexLabel := ![{1, 2}, {1, 4}, {2, 4}]
private def exceptionalRaw : Fin 3 → Finset VertexLabel :=
  ![{0, 1, 2}, {1, 4, 5}, {2, 3, 4}]

private def boundaryEdges : Finset (Finset VertexLabel) :=
  {edgeRaw 0, edgeRaw 1, edgeRaw 2}

abbrev boundary : PreAbstractSimplicialComplex VertexLabel := generated boundaryEdges

abbrev Boundary := Face boundary

private theorem boundary_corner_mem : ∀ i : Fin 3, cornerRaw i ∈ boundary := by
  decide +kernel

private theorem boundary_edge_mem : ∀ i : Fin 3, edgeRaw i ∈ boundary := by
  decide +kernel

private theorem exceptional_mem : ∀ i : Fin 3, exceptionalRaw i ∈ P := by
  decide +kernel

private theorem boundary_facets_mem : ∀ t ∈ boundaryEdges, t ∈ P := by
  decide +kernel

private theorem boundary_le : boundary ≤ P := by
  intro s hs
  obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp hs
  exact (P.isRelLowerSet_faces (boundary_facets_mem t ht)).2 hst hne

def boundaryInclusion : Boundary →o Factor :=
  ⟨fun s => ⟨s.val, boundary_le s.property⟩, fun _ _ h => h⟩

private def boundaryCorner (i : Fin 3) : Boundary := ⟨cornerRaw i, boundary_corner_mem i⟩
private def boundaryEdge (i : Fin 3) : Boundary := ⟨edgeRaw i, boundary_edge_mem i⟩

def corner (i : Fin 3) : Factor := boundaryInclusion (boundaryCorner i)
def exceptional (i : Fin 3) : Factor := ⟨exceptionalRaw i, exceptional_mem i⟩

private theorem edge_le_exceptional : ∀ i : Fin 3, edgeRaw i ⊆ exceptionalRaw i := by
  decide +kernel

private theorem corner_le_edge : ∀ i j : Fin 3, i ≠ j → cornerRaw i ⊆ edgeRaw j := by
  decide +kernel

private theorem edge_endpoints :
    ∀ i : Fin 3, cornerRaw (i + 1) ⊆ edgeRaw i ∧ cornerRaw (i + 2) ⊆ edgeRaw i ∧
      cornerRaw (i + 1) ∪ cornerRaw (i + 2) = edgeRaw i := by
  decide +kernel

private theorem corner_incident :
    ∀ i : Fin 3, cornerRaw i ⊆ edgeRaw (i + 1) ∧ cornerRaw i ⊆ edgeRaw (i + 2) ∧
      exceptionalRaw (i + 1) ∩ exceptionalRaw (i + 2) = cornerRaw i := by
  decide +kernel

private theorem singleton_min :
    ∀ i : Fin 3, ∀ s ∈ (cornerRaw i).powerset, s.Nonempty → s = cornerRaw i := by
  decide +kernel

private theorem edge_only_facet :
    ∀ i : Fin 3, ∀ t ∈ facets, edgeRaw i ⊆ t → t = exceptionalRaw i := by
  decide +kernel

private theorem edge_below_unique_facet (i : Fin 3) (s : Factor)
    (h : edgeRaw i ⊆ s.val) : s.val ⊆ exceptionalRaw i := by
  obtain ⟨_, t, ht, hst⟩ := mem_generated.mp s.property
  rw [← edge_only_facet i t ht (h.trans hst)]
  exact hst

private def Rigid (f : Boundary →o Factor) : Prop :=
  (∀ i : Fin 3, (f (boundaryCorner i)).val = cornerRaw i) ∧
    ∀ i : Fin 3, edgeRaw i ⊆ (f (boundaryEdge i)).val ∧
      (f (boundaryEdge i)).val ⊆ exceptionalRaw i

private theorem rigid_down {f g : Boundary →o Factor} (hfg : g ≤ f) (hf : Rigid f) :
    Rigid g := by
  have corners (i : Fin 3) : (g (boundaryCorner i)).val = cornerRaw i := by
    have h : (g (boundaryCorner i)).val ⊆ (f (boundaryCorner i)).val := hfg (boundaryCorner i)
    rw [hf.1 i] at h
    exact singleton_min i _ (Finset.mem_powerset.mpr h)
      (P.isRelLowerSet_faces (g (boundaryCorner i)).property).1
  refine ⟨corners, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨h₁, h₂, hEdge⟩ := edge_endpoints i
    have h₁' : (g (boundaryCorner (i + 1))).val ⊆ (g (boundaryEdge i)).val :=
      g.monotone (show boundaryCorner (i + 1) ≤ boundaryEdge i from h₁)
    have h₂' : (g (boundaryCorner (i + 2))).val ⊆ (g (boundaryEdge i)).val :=
      g.monotone (show boundaryCorner (i + 2) ≤ boundaryEdge i from h₂)
    rw [corners (i + 1)] at h₁'
    rw [corners (i + 2)] at h₂'
    rw [← hEdge]
    exact Finset.union_subset h₁' h₂'
  · have h : (g (boundaryEdge i)).val ⊆ (f (boundaryEdge i)).val := hfg (boundaryEdge i)
    exact h.trans (hf.2 i).2

private theorem rigid_up {f g : Boundary →o Factor} (hfg : f ≤ g) (hf : Rigid f) :
    Rigid g := by
  have edges (i : Fin 3) : edgeRaw i ⊆ (g (boundaryEdge i)).val ∧
      (g (boundaryEdge i)).val ⊆ exceptionalRaw i := by
    have h : (f (boundaryEdge i)).val ⊆ (g (boundaryEdge i)).val := hfg (boundaryEdge i)
    have h' := (hf.2 i).1.trans h
    exact ⟨h', edge_below_unique_facet i _ h'⟩
  refine ⟨fun i => ?_, edges⟩
  obtain ⟨h₁, h₂, hCorner⟩ := corner_incident i
  have h₁' : (g (boundaryCorner i)).val ⊆ (g (boundaryEdge (i + 1))).val :=
    g.monotone (show boundaryCorner i ≤ boundaryEdge (i + 1) from h₁)
  have h₂' : (g (boundaryCorner i)).val ⊆ (g (boundaryEdge (i + 2))).val :=
    g.monotone (show boundaryCorner i ≤ boundaryEdge (i + 2) from h₂)
  have h := Finset.subset_inter (h₁'.trans (edges (i + 1)).2) (h₂'.trans (edges (i + 2)).2)
  rw [hCorner] at h
  exact singleton_min i _ (Finset.mem_powerset.mpr h)
    (P.isRelLowerSet_faces (g (boundaryCorner i)).property).1

private theorem rigid_fence {f g : Boundary →o Factor} (h : EqvGen (· ≤ ·) f g) :
    Rigid f ↔ Rigid g := by
  induction h with
  | rel _ _ hfg => exact ⟨rigid_up hfg, rigid_down hfg⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The boundary inclusion admits no fence to any constant order map. -/
theorem boundary_not_null (c : Factor) :
    ¬ EqvGen (· ≤ ·) boundaryInclusion (OrderHom.const Boundary c) := by
  intro h
  have hRigid : Rigid boundaryInclusion :=
    ⟨fun _ => rfl, fun i => ⟨Finset.Subset.rfl, edge_le_exceptional i⟩⟩
  have hc := ((rigid_fence h).mp hRigid).1
  have hne : cornerRaw 0 ≠ cornerRaw 1 := by decide +kernel
  have h₀ : c.val = cornerRaw 0 := hc 0
  have h₁ : c.val = cornerRaw 1 := hc 1
  exact hne (h₀.symm.trans h₁)

private theorem map_fence {A B : Type*} [Preorder A] [Preorder B]
    (f : A → B) (hf : Monotone f) {a b : A} (h : EqvGen (· ≤ ·) a b) :
    EqvGen (· ≤ ·) (f a) (f b) := by
  induction h with
  | rel a b hab => exact .rel _ _ (hf hab)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem boundary_edge_index :
    ∀ t ∈ boundaryEdges, ∃ i : Fin 3, t = edgeRaw i := by
  decide +kernel

private theorem boundary_below_exceptional (s : Boundary) :
    ∃ i : Fin 3, boundaryInclusion s ≤ exceptional i := by
  obtain ⟨_, t, ht, hst⟩ := mem_generated.mp s.property
  obtain ⟨i, rfl⟩ := boundary_edge_index t ht
  exact ⟨i, hst.trans (edge_le_exceptional i)⟩

private theorem projected_noncategorical {U : Set ProductPoset} (embed : Boundary →o U)
    (project : ProductPoset →o Factor)
    (hProject : ∀ s, project (embed s).val = boundaryInclusion s) : ¬ Categorical U := by
  rintro ⟨c, hc⟩
  let projectFence (f : U →o ProductPoset) : Boundary →o Factor :=
    project.comp (f.comp embed)
  have h := map_fence projectFence
    (fun _ _ hfg s => project.monotone (OrderHom.le_def.mp hfg (embed s))) hc
  have hstart : projectFence (OrderEmbedding.subtype U).toOrderHom = boundaryInclusion := by
    apply OrderHom.ext
    funext s
    exact hProject s
  have hend : projectFence (OrderHom.const U c) = OrderHom.const Boundary (project c) := by
    apply OrderHom.ext
    rfl
  rw [hstart, hend] at h
  exact boundary_not_null (project c) h

/-- A lower set containing the three exceptional faces over one common face
contains a slice whose first projection recovers the rigid boundary. -/
theorem first_slice_noncategorical {U : Set ProductPoset} (hU : IsLowerSet U) (b : Factor)
    (h : ∀ i : Fin 3, (exceptional i, b) ∈ U) : ¬ Categorical U := by
  have sliceMem (s : Boundary) : (boundaryInclusion s, b) ∈ U := by
    obtain ⟨i, hi⟩ := boundary_below_exceptional s
    exact hU (show (boundaryInclusion s, b) ≤ (exceptional i, b) from ⟨hi, le_rfl⟩) (h i)
  let embed : Boundary →o U :=
    ⟨fun s => ⟨(boundaryInclusion s, b), sliceMem s⟩,
      fun _ _ hst => ⟨boundaryInclusion.monotone hst, le_rfl⟩⟩
  exact projected_noncategorical embed OrderHom.fst (fun _ => rfl)

/-- A lower set containing the three exceptional faces in one row has the
corresponding rigid slice under the second projection. -/
theorem second_slice_noncategorical {U : Set ProductPoset} (hU : IsLowerSet U) (a : Factor)
    (h : ∀ j : Fin 3, (a, exceptional j) ∈ U) : ¬ Categorical U := by
  have sliceMem (s : Boundary) : (a, boundaryInclusion s) ∈ U := by
    obtain ⟨j, hj⟩ := boundary_below_exceptional s
    exact hU (show (a, boundaryInclusion s) ≤ (a, exceptional j) from ⟨le_rfl, hj⟩) (h j)
  let embed : Boundary →o U :=
    ⟨fun s => ⟨(a, boundaryInclusion s), sliceMem s⟩,
      fun _ _ hst => ⟨le_rfl, boundaryInclusion.monotone hst⟩⟩
  exact projected_noncategorical embed OrderHom.snd (fun _ => rfl)

/-- A colour either meets every row in a fixed pair of columns or fills a row. -/
def SpansSlice (paint : Fin 3 → Fin 3 → Fin 2) (colour : Fin 2) : Prop :=
  (∃ j k : Fin 3, j ≠ k ∧ ∀ i : Fin 3, paint i j = colour ∨ paint i k = colour) ∨
    (∃ i : Fin 3, ∀ j : Fin 3, paint i j = colour)

private def entries (a b c d e f g h i : Fin 2) : Fin 3 → Fin 3 → Fin 2 :=
  ![![a, b, c], ![d, e, f], ![g, h, i]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks all 512 matrices.
private theorem entries_span_slice :
    ∀ a b c d e f g h i : Fin 2,
      ∃ colour : Fin 2, SpansSlice (entries a b c d e f g h i) colour := by
  unfold SpansSlice
  decide +kernel

/-- Every two-colouring of the 3-by-3 array supplies a slice of one colour. -/
theorem two_colour_spans_slice (paint : Fin 3 → Fin 3 → Fin 2) :
    ∃ colour : Fin 2, SpansSlice paint colour := by
  have h :
      entries (paint 0 0) (paint 0 1) (paint 0 2)
        (paint 1 0) (paint 1 1) (paint 1 2)
        (paint 2 0) (paint 2 1) (paint 2 2) = paint := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← h]
  exact entries_span_slice _ _ _ _ _ _ _ _ _

private theorem remaining_corner :
    ∀ j k : Fin 3, j ≠ k → ∃ l : Fin 3, l ≠ j ∧ l ≠ k := by
  decide +kernel

theorem no_categorical_cover_two : ¬ HasCategoricalCover ProductPoset 2 := by
  rintro ⟨U, hU, hCover⟩
  classical
  let paint (i j : Fin 3) : Fin 2 := Classical.choose (hCover (exceptional i, exceptional j))
  have hPaint (i j : Fin 3) : (exceptional i, exceptional j) ∈ U (paint i j) :=
    Classical.choose_spec (hCover (exceptional i, exceptional j))
  obtain ⟨colour, hSlice⟩ := two_colour_spans_slice paint
  obtain ⟨hLower, hCat⟩ := hU colour
  unfold SpansSlice at hSlice
  rcases hSlice with ⟨j, k, hjk, hRows⟩ | ⟨i, hRow⟩
  · obtain ⟨l, hlj, hlk⟩ := remaining_corner j k hjk
    have hBelow (m : Fin 3) (hlm : l ≠ m) : corner l ≤ exceptional m :=
      (corner_le_edge l m hlm).trans (edge_le_exceptional m)
    refine first_slice_noncategorical hLower (corner l) ?_ hCat
    intro i
    rcases hRows i with hi | hi
    · exact hLower (show (exceptional i, corner l) ≤ (exceptional i, exceptional j)
        from ⟨le_rfl, hBelow j hlj⟩) (hi ▸ hPaint i j)
    · exact hLower (show (exceptional i, corner l) ≤ (exceptional i, exceptional k)
        from ⟨le_rfl, hBelow k hlk⟩) (hi ▸ hPaint i k)
  · exact second_slice_noncategorical hLower (exceptional i)
      (fun j => hRow j ▸ hPaint i j) hCat

private def keptFacets (i : Fin 3) : Finset (Finset VertexLabel) :=
  facets.erase (exceptionalRaw i)

/-- The factor piece consists of the faces of the six retained facets. -/
def factorPiece (i : Fin 3) : Set Factor := {s | s.val ∈ generated (keptFacets i)}

/-- The three lower cover members use the same retained facets in both factors. -/
def rectangle (i : Fin 3) : Set ProductPoset :=
  {x | x.1 ∈ factorPiece i ∧ x.2 ∈ factorPiece i}

private theorem factorPiece_lower (i : Fin 3) : IsLowerSet (factorPiece i) := by
  intro b a hab hb
  change a.val ∈ generated (keptFacets i)
  exact ((generated (keptFacets i)).isRelLowerSet_faces hb).2
    (show a.val ⊆ b.val from hab) (P.isRelLowerSet_faces a.property).1

private theorem rectangle_lower (i : Fin 3) : IsLowerSet (rectangle i) := by
  intro a b hab hb
  exact ⟨factorPiece_lower i hab.1 hb.1, factorPiece_lower i hab.2 hb.2⟩

private theorem facets_share_piece :
    ∀ t ∈ facets, ∀ u ∈ facets, ∃ i : Fin 3, t ∈ keptFacets i ∧ u ∈ keptFacets i := by
  decide +kernel

private theorem rectangles_cover (x : ProductPoset) : ∃ i : Fin 3, x ∈ rectangle i := by
  obtain ⟨hne₁, t, ht, hst⟩ := mem_generated.mp x.1.property
  obtain ⟨hne₂, u, hu, hsu⟩ := mem_generated.mp x.2.property
  obtain ⟨i, hit, hiu⟩ := facets_share_piece t ht u hu
  refine ⟨i, ?_⟩
  change x.1.val ∈ generated (keptFacets i) ∧ x.2.val ∈ generated (keptFacets i)
  exact ⟨mem_generated.mpr ⟨hne₁, t, hit, hst⟩, mem_generated.mpr ⟨hne₂, u, hiu, hsu⟩⟩

-- The last two rows are the rotations of the first by (1 2 4)(0 3 5).
private def foldPair : Fin 3 → Fin 5 → VertexLabel × VertexLabel :=
  ![![(1, 5), (0, 3), (2, 3), (5, 3), (4, 3)],
    ![(4, 3), (5, 0), (1, 0), (3, 0), (2, 0)],
    ![(2, 0), (3, 5), (4, 5), (0, 5), (1, 5)]]

private def foldVertex (i : Fin 3) : ℕ → VertexLabel → VertexLabel
  | 0, v => v
  | k + 1, v =>
    let w := foldVertex i k v
    let p := foldPair i (Fin.ofNat 5 k)
    if w = p.1 then p.2 else w

private def finalVertex : Fin 3 → VertexLabel := ![3, 0, 5]

private theorem final_vertex_mem : ∀ i : Fin 3, ({finalVertex i} : Finset VertexLabel) ∈ P := by
  decide +kernel

private theorem fold_end : ∀ (i : Fin 3) (v : VertexLabel), foldVertex i 5 v = finalVertex i := by
  decide +kernel

private theorem fold_image_table :
    ∀ (i : Fin 3) (k : Fin 6), ∀ t ∈ keptFacets i, t.image (foldVertex i k.val) ∈ P := by
  decide +kernel

private theorem fold_union_table :
    ∀ (i : Fin 3) (k : Fin 5), ∀ t ∈ keptFacets i,
      t.image (foldVertex i k.castSucc.val) ∪ t.image (foldVertex i k.succ.val) ∈ P := by
  decide +kernel

private def foldMap (i : Fin 3) (k : Fin 6) : factorPiece i →o Factor where
  toFun s := ⟨s.val.val.image (foldVertex i k.val), by
    obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp
      (show s.val.val ∈ generated (keptFacets i) from s.property)
    exact (P.isRelLowerSet_faces (fold_image_table i k t ht)).2
      (Finset.image_subset_image hst) (hne.image _)⟩
  monotone' _ _ h := Finset.image_subset_image h

private def unionMap (i : Fin 3) (k : Fin 5) : factorPiece i →o Factor where
  toFun s :=
    ⟨s.val.val.image (foldVertex i k.castSucc.val) ∪ s.val.val.image (foldVertex i k.succ.val), by
      obtain ⟨hne, t, ht, hst⟩ := mem_generated.mp
        (show s.val.val ∈ generated (keptFacets i) from s.property)
      exact (P.isRelLowerSet_faces (fold_union_table i k t ht)).2
        (Finset.union_subset_union (Finset.image_subset_image hst) (Finset.image_subset_image hst))
        ((hne.image _).mono Finset.subset_union_left)⟩
  monotone' _ _ h :=
    Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

private theorem fold_step (i : Fin 3) (k : Fin 5) :
    EqvGen (· ≤ ·) (foldMap i k.castSucc) (foldMap i k.succ) := by
  have h₁ : foldMap i k.castSucc ≤ unionMap i k := fun _ => Finset.subset_union_left
  have h₂ : foldMap i k.succ ≤ unionMap i k := fun _ => Finset.subset_union_right
  exact .trans _ _ _ (.rel _ _ h₁) (.symm _ _ (.rel _ _ h₂))

private theorem factor_categorical (i : Fin 3) : Categorical (factorPiece i) := by
  let c : Factor := ⟨{finalVertex i}, final_vertex_mem i⟩
  have hStart : foldMap i 0 = (OrderEmbedding.subtype (factorPiece i)).toOrderHom := by
    apply OrderHom.ext
    funext s
    apply Subtype.ext
    change s.val.val.image id = s.val.val
    exact Finset.image_id
  have hEnd : foldMap i 5 = OrderHom.const (factorPiece i) c := by
    apply OrderHom.ext
    funext s
    apply Subtype.ext
    change s.val.val.image (foldVertex i 5) = {finalVertex i}
    rw [show foldVertex i 5 = (fun _ => finalVertex i) from funext (fold_end i)]
    exact Finset.image_const (P.isRelLowerSet_faces s.val.property).1 (finalVertex i)
  have h : EqvGen (· ≤ ·) (foldMap i 0) (foldMap i 5) :=
    .trans _ _ _ (fold_step i 0)
      (.trans _ _ _ (fold_step i 1)
        (.trans _ _ _ (fold_step i 2) (.trans _ _ _ (fold_step i 3) (fold_step i 4))))
  rw [hStart, hEnd] at h
  exact ⟨c, h⟩

private theorem rectangle_categorical (i : Fin 3) : Categorical (rectangle i) := by
  obtain ⟨c, hc⟩ := factor_categorical i
  let both (f : factorPiece i →o Factor) : rectangle i →o ProductPoset :=
    ⟨fun x => (f ⟨x.val.1, x.property.1⟩, f ⟨x.val.2, x.property.2⟩),
      fun _ _ h => ⟨f.monotone h.1, f.monotone h.2⟩⟩
  have h := map_fence both
    (fun _ _ hfg x => ⟨hfg ⟨x.val.1, x.property.1⟩, hfg ⟨x.val.2, x.property.2⟩⟩) hc
  have hStart : both (OrderEmbedding.subtype (factorPiece i)).toOrderHom =
      (OrderEmbedding.subtype (rectangle i)).toOrderHom := by
    apply OrderHom.ext
    rfl
  have hEnd : both (OrderHom.const (factorPiece i) c) =
      OrderHom.const (rectangle i) (c, c) := by
    apply OrderHom.ext
    rfl
  rw [hStart, hEnd] at h
  exact ⟨(c, c), h⟩

theorem has_categorical_cover_three : HasCategoricalCover ProductPoset 3 :=
  ⟨rectangle, fun i => ⟨rectangle_lower i, rectangle_categorical i⟩, rectangles_cover⟩

/-- Three categorical lower sets cover the original product of nonempty face
posets, and two cannot cover it. -/
theorem categorical_cover_three_not_two :
    HasCategoricalCover (Face P × Face P) 3 ∧ ¬ HasCategoricalCover (Face P × Face P) 2 :=
  ⟨has_categorical_cover_three, no_categorical_cover_two⟩

/-- The least size of a categorical lower cover of the original product is three. -/
theorem least_categorical_cover :
    IsLeast {n : ℕ | HasCategoricalCover (Face P × Face P) n} 3 := by
  refine ⟨has_categorical_cover_three, ?_⟩
  intro n hn
  change HasCategoricalCover ProductPoset n at hn
  by_contra h
  have hn₂ : n ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
  obtain ⟨U, hU, hCover⟩ := hn
  obtain ⟨fallback, _⟩ := hCover (corner 0, corner 0)
  let pick (i : Fin 2) : Fin n := if hi : i.val < n then ⟨i.val, hi⟩ else fallback
  apply no_categorical_cover_two
  refine ⟨fun i => U (pick i), fun i => hU (pick i), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hCover x
  refine ⟨⟨i.val, i.isLt.trans_le hn₂⟩, ?_⟩
  simpa [pick, i.isLt] using hi

end D5.S3.Topology.ProductRigidCores
