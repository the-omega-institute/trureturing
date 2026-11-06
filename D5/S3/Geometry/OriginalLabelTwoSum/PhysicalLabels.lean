/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalLabels
   generality: G
   digest: Injective label transport of actual graph data and its unique-path rows. -/
import D5.S3.Geometry.OriginalLabelTwoSum.GraphDataCore
import D5.S3.Geometry.OriginalLabelTwoSum.Rename

/-! SOURCE_ONLY_UNCOMPILED. Only labels change; the graph, tree and chord
endpoints are inherited. Inactive coordinates have an explicit total value. -/
noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalLabels
variable {A L V : Type*} [Fintype L] [DecidableEq L]
  [Fintype V] [DecidableEq V]

def edge (g : GraphData A L) (f : L ↪ V) (fallback : Sym2 A) (i : V) : Sym2 A :=
  if h : ∃ j : L, f j = i then g.edge (Classical.choose h) else fallback

theorem edge_image (g : GraphData A L) (f : L ↪ V) (fallback : Sym2 A) (j : L) :
    edge g f fallback (f j) = g.edge j := by
  have h : ∃ k : L, f k = f j := ⟨j,rfl⟩
  rw [edge,dif_pos h]
  exact congrArg g.edge (f.injective (Classical.choose_spec h))

def data (g : GraphData A L) (f : L ↪ V) (fallback : Sym2 A) : GraphData A V where
  graph := g.graph
  tree := g.tree
  tree_le := g.tree_le
  isTree := g.isTree
  ground := g.ground.image f
  edge := edge g f fallback
  tree_edges := by
    intro x y
    rw [g.tree_edges x y]
    constructor
    · rintro ⟨j,hj,he⟩
      exact ⟨f j,Finset.mem_image.mpr ⟨j,hj,rfl⟩,(edge_image g f fallback j).trans he⟩
    · rintro ⟨i,hi,he⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j,hj,(edge_image g f fallback j).symm.trans he⟩
  labels_injective := by
    intro i hi j hj he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    rw [edge_image,edge_image] at he
    exact congrArg f (g.labels_injective u hu v hv he)
  chords := g.chords
  start := g.start
  finish := g.finish
  chord_adj := g.chord_adj
  chord_not_tree := g.chord_not_tree
  chord_cover := g.chord_cover

theorem row (g : GraphData A L) (f : L ↪ V) (fallback : Sym2 A) (c : g.chords) :
    (data g f fallback).rows.row c = (g.rows.row c).image f := by
  classical
  ext i
  change (i ∈ (g.ground.image f).filter (fun j => edge g f fallback j ∈
      (g.path c).edges)) ↔ i ∈ (g.ground.filter
        (fun j => g.edge j ∈ (g.path c).edges)).image f
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨j,hj,rfl⟩,hp⟩
    exact ⟨j,⟨hj,by rwa [edge_image] at hp⟩,rfl⟩
  · rintro ⟨j,⟨hj,hp⟩,rfl⟩
    exact ⟨⟨j,hj,rfl⟩,by rw [edge_image]; exact hp⟩

theorem root (g : GraphData A L) (f : L ↪ V) (fallback : Sym2 A) :
    (data g f fallback).rows.root = renameFamily f g.rows.root := by
  apply SetLike.ext
  intro s
  change (∃ c : g.chords, s ⊆ g.ground.image f \ (data g f fallback).rows.row c) ↔
    ∃ t, (∃ c : g.chords, t ⊆ g.ground \ g.rows.row c) ∧ t.image f = s
  simp_rw [row,← Finset.image_sdiff _ _ f.injective]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp hc
    exact ⟨t,⟨c,ht⟩,he⟩
  · rintro ⟨t,⟨c,ht⟩,rfl⟩
    exact ⟨c,Finset.image_subset_image ht⟩

end D5.S3.Geometry.OriginalLabelTwoSum.PhysicalLabels
