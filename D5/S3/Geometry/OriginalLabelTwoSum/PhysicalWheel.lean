/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel
   mirror-E: none(waiver:original-label-physical-wheel)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Star]
   utility: none
   digest: Fixed W4 actual physical gluing on arbitrary original ambient labels, retaining all ghosts. -/
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue
import D5.S3.Geometry.OriginalLabelTwoSum.Rename

/-! SOURCE ONLY, UNCOMPILED. This installs the released actual W4 graph on
the caller's original label type. It does not assert a native certificate,
history, arbitrary marked wheel or universal structural supplier. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel
variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

/-- Every original wheel label, even its nonground zero, has its prescribed
total value. Additional ambient ghosts get the explicit hub loop. -/
def ambientEdge (f : Label ↪ Ambient) (i : Ambient) : Sym2 Label :=
  if h : ∃ j : Label, f j = i then wheelGraphData.edge (Classical.choose h) else s(0,0)

theorem ambientEdge_image (f : Label ↪ Ambient) (j : Label) :
    ambientEdge f (f j) = wheelGraphData.edge j := by
  have h : ∃ k : Label, f k = f j := ⟨j,rfl⟩
  rw [ambientEdge,dif_pos h]
  exact congrArg wheelGraphData.edge (f.injective (Classical.choose_spec h))

/-- Only the labels change ambient type. The ACTUAL wheel graph, entire tree,
original four indices and endpoints are inherited literally. -/
def ambientGraph (f : Label ↪ Ambient) : GraphData Label Ambient where
  graph := wheelGraphData.graph
  tree := wheelGraphData.tree
  tree_le := wheelGraphData.tree_le
  isTree := wheelGraphData.isTree
  ground := Y.image f
  edge := ambientEdge f
  tree_edges := by
    intro x y
    rw [wheelGraphData.tree_edges x y]
    constructor
    · rintro ⟨j,hj,he⟩
      exact ⟨f j,Finset.mem_image.mpr ⟨j,hj,rfl⟩,(ambientEdge_image f j).trans he⟩
    · rintro ⟨i,hi,he⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j,hj,(ambientEdge_image f j).symm.trans he⟩
  labels_injective := by
    intro i hi j hj he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    rw [ambientEdge_image,ambientEdge_image] at he
    exact congrArg f (wheelGraphData.labels_injective u hu v hv he)
  chords := wheelGraphData.chords
  start := wheelGraphData.start
  finish := wheelGraphData.finish
  chord_adj := wheelGraphData.chord_adj
  chord_not_tree := wheelGraphData.chord_not_tree
  chord_cover := wheelGraphData.chord_cover

local instance : OfNat wheelGraphData.chords 0 :=
  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=
  inferInstanceAs (OfNat (Fin 4) 0)

theorem ambient_row (f : Label ↪ Ambient) (c : Fin 4) :
    (ambientGraph f).rows.row c = (wheelGraphData.rows.row c).image f := by
  classical
  have hp : (ambientGraph f).path c = wheelGraphData.path c :=
    (ambientGraph f).path_eq c _
      (Classical.choose_spec (wheelGraphData.isTree.existsUnique_path _ _)).1
  ext i
  simp only [GraphData.rows,Finset.mem_filter,Finset.mem_image]
  rw [hp]
  change (i ∈ Y.image f ∧ ambientEdge f i ∈ (wheelGraphData.path c).edges) ↔ _
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨⟨j,hj,rfl⟩,hp⟩
    exact ⟨j,⟨hj,by rwa [ambientEdge_image] at hp⟩,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨j,hj.1,rfl⟩,by rw [ambientEdge_image]; exact hj.2⟩

theorem ambient_uniqueInterface (f : Label ↪ Ambient) :
    (ambientGraph f).UniqueInterface (0 : Fin 4) := by
  intro d hd
  exact wheel_uniqueInterface d hd

/-- Physical deletion uses every original surviving W4 index. This proof
consumes wheel_E_edge, and does not infer physical deletion from row equality. -/
theorem ambient_E_edge (f : Label ↪ Ambient) :
    (ambientGraph f).E_edge (0 : Fin 4) = renameFamily f E := by
  have h : (ambientGraph f).E_edge (0 : Fin 4) =
      renameFamily f (wheelGraphData.E_edge (0 : Fin 4)) := by
    apply SetLike.ext
    intro s
    change (∃ d : wheelGraphData.PhysicalSurvivor (0 : Fin 4),
      s ⊆ Y.image f \ (ambientGraph f).rows.row d.1) ↔
      ∃ t, (∃ d : wheelGraphData.PhysicalSurvivor (0 : Fin 4),
        t ⊆ Y \ wheelGraphData.rows.row d.1) ∧ t.image f = s
    simp_rw [ambient_row, ← Finset.image_sdiff _ _ f.injective]
    constructor
    · rintro ⟨d,hd⟩
      obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp hd
      exact ⟨t,⟨d,ht⟩,he⟩
    · rintro ⟨t,⟨d,ht⟩,rfl⟩
      exact ⟨d,Finset.image_subset_image ht⟩
  rw [h,wheel_E_edge]

theorem ambient_without (f : Label ↪ Ambient) :
    ((ambientGraph f).rows.without (0 : Fin 4)).root = renameFamily f E := by
  rw [← (ambientGraph f).E_edge_eq_without 0 (ambient_uniqueInterface f)]
  exact ambient_E_edge f

theorem zero_outside_ground (f : Label ↪ Ambient) : f 0 ∉ Y.image f := by
  intro hi
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
  have hj0 := f.injective he
  subst j
  exact (by decide : (0 : Label) ∉ Y) hj

/-- Any retained left edge, with arbitrary original ambient labels and ghosts.
The injection specifies the five literal W4 labels; f(0) is NOT retained. -/
def ambientGlue (left : GraphData VL Ambient) (X : Finset Ambient) (e : Ambient)
    (a b : VL) (hleft : left.ground = insert e X) (hedge : left.edge e = s(a,b))
    (f : Label ↪ Ambient) (hf0 : f 0 = e) (heX : e ∉ X)
    (hXY : Disjoint X (Y.image f)) : PhysicalGlue VL Label Ambient where
  left := left
  right := ambientGraph f
  selected := 0
  X := X
  Y := Y.image f
  e := e
  left_ground := hleft
  right_ground := rfl
  e_not_X := heX
  e_not_Y := hf0 ▸ zero_outside_ground f
  disjoint := hXY
  aL := a
  bL := b
  edge_e := hedge

/-- Actual graph-derived fixed-W4 parent formula on original ambient values,
with unchanged X, Y.image f and all labels outside their union still ambient. -/
theorem ambient_actual_root (left : GraphData VL Ambient) (X : Finset Ambient) (e : Ambient)
    (a b : VL) (hleft : left.ground = insert e X) (hedge : left.edge e = s(a,b))
    (f : Label ↪ Ambient) (hf0 : f 0 = e) (heX : e ∉ X)
    (hXY : Disjoint X (Y.image f)) :
    (ambientGlue left X e a b hleft hedge f hf0 heX hXY).data.rows.root =
      phi X (Y.image f) (Z.image f) (restrict X left.rows.root)
        (rawLink X e left.rows.root) (renameFamily f E) := by
  have ht := (ambientGlue left X e a b hleft hedge f hf0 heX hXY).root_formula
  have hr : (ambientGraph f).rows.row (0 : Fin 4) = R.image f := by
    exact (ambient_row f 0).trans (congrArg (fun t : Finset Label => t.image f) (fundamental_rows 0))
  have hz : Y.image f \ R.image f = Z.image f := by
    rw [← Finset.image_sdiff _ _ f.injective]
    exact congrArg (fun t : Finset Label => t.image f) (by decide : Y \ R = Z)
  simpa only [ambientGlue,hr,hz,ambient_E_edge] using ht

/-- The local U* literal consumer uses the actual ambient wheel's original
three survivor indices. No global injectivity premise is added to PhysicalGlue. -/
theorem ambient_actual_literal_root (left : GraphData VL Ambient) (X : Finset Ambient) (e : Ambient)
    (a b : VL) (hleft : left.ground = insert e X) (hedge : left.edge e = s(a,b))
    (f : Label ↪ Ambient) (hf0 : f 0 = e) (heX : e ∉ X)
    (hXY : Disjoint X (Y.image f)) :
    (ambientGlue left X e a b hleft hedge f hf0 heX hXY).data.rows.root =
      phi X (Y.image f) (Z.image f) (restrict X left.rows.root)
        (rawLink X e left.rows.root) ((ambientGraph f).rows.without (0 : Fin 4)).root := by
  rw [ambient_without]
  exact ambient_actual_root left X e a b hleft hedge f hf0 heX hXY

end D5.S3.Geometry.OriginalLabelTwoSum.Wheel
