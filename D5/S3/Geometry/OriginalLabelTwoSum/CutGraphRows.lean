/- GID: D5/S3/Geometry/OriginalLabelTwoSum/CutGraphRows
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/CutGraphRows
   mirror-E: none(waiver:original-label-cut-graph-rows)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: GraphData consumes the proved actual cut-tree paths and derives original-label row substitution prerequisites without finite vertices. -/
import D5.S3.Geometry.OriginalLabelTwoSum.CutPaths
import D5.S3.Geometry.OriginalLabelTwoSum.GraphDataCore

/-! SOURCE ONLY. The original LowerSet Family and Rows remain authoritative.
This module proves path-derived row substitution, not a parent GraphData root,
chord-index deletion, graph history, or native certificate. -/
noncomputable section
open SimpleGraph Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum

structure GraphSource (VL VR LL LR : Type*) [Fintype LL] [DecidableEq LL]
    [Fintype LR] [DecidableEq LR] where
  left : GraphData VL LL
  right : GraphData VR LR
  aL bL : VL
  aR bR : VR
  htermR : aR ≠ bR
  e : LL
  he : e ∈ left.ground
  edge_e : left.edge e = s(aL,bL)

namespace GraphSource
variable {VL VR LL LR : Type*} [Fintype LL] [DecidableEq LL]
  [Fintype LR] [DecidableEq LR] (source : GraphSource VL VR LL LR)

/-- The original labelled tree-edge equation supplies adjacency. In particular
left terminal distinctness is derived from actual looplessness. -/
theorem terminal_adj : source.left.tree.Adj source.aL source.bL :=
  (source.left.tree_edges _ _).mpr ⟨source.e,source.he,source.edge_e⟩

/-- Entry point into the arbitrary-carrier construction: no finite Vertex
instance and no parent-tree/path fact is supplied by this record. -/
def input : CutTree.Input VL VR where
  TL := source.left.tree
  TR := source.right.tree
  aL := source.aL
  bL := source.bL
  aR := source.aR
  bR := source.bR
  neL := source.terminal_adj.ne
  neR := source.htermR
  leftTree := source.left.isTree
  rightTree := source.right.isTree
  edge := source.terminal_adj

theorem actual_tree : source.input.tree.IsTree := source.input.isTree

private theorem graphPath_isPath {V L : Type*} [Fintype L] [DecidableEq L]
    (g : GraphData V L) (c : g.chords) : (g.path c).IsPath :=
  (Classical.choose_spec (g.isTree.existsUnique_path (g.start c) (g.finish c))).1

private theorem labelled_edge {V L : Type*} [Fintype L] [DecidableEq L]
    (g : GraphData V L) {i : L} (hi : i ∈ g.ground) : g.edge i ∈ g.tree.edgeSet := by
  have h : ∀ d : Sym2 V, g.edge i = d → d ∈ g.tree.edgeSet := by
    apply Sym2.ind
    intro x y he
    exact (g.tree_edges x y).mpr ⟨i,hi,he⟩
  exact h _ rfl

private theorem retained_edge {i : LL} (hi : i ∈ source.left.ground)
    (hne : i ≠ source.e) : source.left.edge i ∈ source.input.cut.edgeSet := by
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨labelled_edge source.left hi,?_⟩
  simp only [Set.mem_singleton_iff]
  intro he
  apply hne
  exact source.left.labels_injective i hi source.e source.he (he.trans source.edge_e.symm)

private theorem cross_ne {d : Sym2 VL} {f : Sym2 VR}
    (hd : d ∈ source.input.cut.edgeSet) (hf : f ∈ source.right.tree.edgeSet) :
    Sym2.map source.input.qL d ≠ Sym2.map source.input.qR f := by
  intro he
  exact Set.disjoint_left.mp source.input.edge_images_disjoint
    ⟨d,hd,rfl⟩ ⟨f,hf,he.symm⟩

/-- Original ambient labels are retained with their summand tags. -/
def labelEdge : LL ⊕ LR → Sym2 source.input.Carrier
  | .inl i => Sym2.map source.input.qL (source.left.edge i)
  | .inr j => Sym2.map source.input.qR (source.right.edge j)

def ground : Finset (LL ⊕ LR) :=
  (source.left.ground.erase source.e).image Sum.inl ∪ source.right.ground.image Sum.inr

def terminalRow : Finset LR := by
  classical
  exact source.right.ground.filter (fun j =>
    source.right.edge j ∈ (source.input.rightPath source.aR source.bR).edges)

/-- Rows computed from the ACTUAL constructed tree paths, before any chord
index restriction or root formula is chosen. -/
def actualLeftRow (c : source.left.chords) : Finset (LL ⊕ LR) := by
  classical
  exact source.ground.filter (fun i => source.labelEdge i ∈
    (source.input.path (source.input.qL (source.left.start c))
      (source.input.qL (source.left.finish c))).edges)

def actualRightRow (c : source.right.chords) : Finset (LL ⊕ LR) := by
  classical
  exact source.ground.filter (fun i => source.labelEdge i ∈
    (source.input.path (source.input.qR (source.right.start c))
      (source.input.qR (source.right.finish c))).edges)

/-- Every retained original left label has exactly its old path membership. -/
theorem left_label_mem (c : source.left.chords) {i : LL}
    (hi : i ∈ source.left.ground) (hne : i ≠ source.e) :
    Sym2.map source.input.qL (source.left.edge i) ∈
      (source.input.path (source.input.qL (source.left.start c))
        (source.input.qL (source.left.finish c))).edges ↔ i ∈ source.left.rows.row c := by
  rw [source.input.left_path_edge_mem (source.left.path c) (graphPath_isPath _ _)]
  simp only [GraphData.rows, Finset.mem_filter]
  constructor
  · rintro (⟨d,hd,_,he⟩ | ⟨_,d,hd,he⟩)
    · have hdi := Sym2.map.injective source.input.qL_injective he
      exact ⟨hi,hdi ▸ hd⟩
    · exact False.elim (source.cross_ne (source.retained_edge hi hne)
        ((source.input.rightPath _ _).edges_subset_edgeSet hd) he.symm)
  · rintro ⟨_,hiPath⟩
    refine Or.inl ⟨_,hiPath,?_,rfl⟩
    intro he
    exact hne (source.left.labels_injective i hi source.e source.he
      (he.trans source.edge_e.symm))

/-- A right label enters a left path exactly when the deleted left edge occurs
and that right label belongs to the genuine right terminal path. -/
theorem right_label_in_left (c : source.left.chords) {j : LR}
    (hj : j ∈ source.right.ground) :
    Sym2.map source.input.qR (source.right.edge j) ∈
      (source.input.path (source.input.qL (source.left.start c))
        (source.input.qL (source.left.finish c))).edges ↔
      source.e ∈ source.left.rows.row c ∧ j ∈ source.terminalRow := by
  rw [source.input.left_path_edge_mem (source.left.path c) (graphPath_isPath _ _)]
  have hmark : source.e ∈ source.left.rows.row c ↔
      s(source.aL,source.bL) ∈ (source.left.path c).edges := by
    simp only [GraphData.rows, Finset.mem_filter, source.he, true_and, source.edge_e]
  rw [hmark]
  simp only [terminalRow, Finset.mem_filter]
  constructor
  · rintro (⟨d,hd,hne,he⟩ | ⟨he,d,hd,hmap⟩)
    · have hc : d ∈ source.input.cut.edgeSet := by
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨(source.left.path c).edges_subset_edgeSet hd,by simpa using hne⟩
      exact False.elim (source.cross_ne hc (labelled_edge source.right hj) he)
    · have hdj := Sym2.map.injective source.input.qR_injective hmap
      exact ⟨he,hj,hdj ▸ hd⟩
  · rintro ⟨he,_,hjPath⟩
    exact Or.inr ⟨he,_,hjPath,rfl⟩

/-- The exact original-label row substitution prerequisite of G1B. It is a
consequence of actual paths, and makes no assumption about graph roots. -/
theorem left_row_substitution (c : source.left.chords) :
    source.actualLeftRow c =
      ((source.left.rows.row c).erase source.e).image Sum.inl ∪
      (if source.e ∈ source.left.rows.row c then
        source.terminalRow.image Sum.inr else ∅) := by
  classical
  ext i
  cases i with
  | inl i =>
    have hrow := source.left.rows.row_supported c
    by_cases hi : i ∈ source.left.ground
    · by_cases hne : i ≠ source.e
      · have hp := source.left_label_mem c hi hne
        simpa [actualLeftRow,ground,labelEdge,hi,hne,Finset.mem_image] using hp
      · have he : i = source.e := not_ne_iff.mp hne
        subst i
        simp [actualLeftRow,ground,Finset.mem_image]
    · have hn : i ∉ source.left.rows.row c := fun h => hi (hrow h)
      simp [actualLeftRow,ground,hi,hn,Finset.mem_image]
  | inr j =>
    by_cases hj : j ∈ source.right.ground
    · have hp := source.right_label_in_left c hj
      by_cases he : source.e ∈ source.left.rows.row c <;>
        simpa [actualLeftRow,ground,labelEdge,hj,he,Finset.mem_image] using hp
    · have ht : j ∉ source.terminalRow := by simp [terminalRow,hj]
      simp [actualLeftRow,ground,hj,ht,Finset.mem_image]

/-- Every right original row is inherited unchanged, with its summand tag. -/
theorem right_row_inheritance (c : source.right.chords) :
    source.actualRightRow c = (source.right.rows.row c).image Sum.inr := by
  classical
  ext i
  cases i with
  | inl i =>
    by_cases hi : i ∈ source.left.ground ∧ i ≠ source.e
    · have hn : Sym2.map source.input.qL (source.left.edge i) ∉
          (source.input.path (source.input.qR (source.right.start c))
            (source.input.qR (source.right.finish c))).edges := by
        rw [source.input.right_path_edge_mem]
        rintro ⟨d,hd,he⟩
        exact source.cross_ne (source.retained_edge hi.1 hi.2)
          ((source.input.rightPath _ _).edges_subset_edgeSet hd) he.symm
      simp [actualRightRow,ground,labelEdge,hn,Finset.mem_image]
    · simp [actualRightRow,ground,Finset.mem_image,Finset.mem_erase,hi,and_comm]
  | inr j =>
    have hp : Sym2.map source.input.qR (source.right.edge j) ∈
        (source.input.path (source.input.qR (source.right.start c))
          (source.input.qR (source.right.finish c))).edges ↔
        source.right.edge j ∈ (source.right.path c).edges := by
      rw [source.input.right_path_edge_mem]
      have heq := source.right.path_eq c
        (source.input.rightPath (source.right.start c) (source.right.finish c))
        (CutTree.treePath_isPath _ _ _)
      rw [heq]
      constructor
      · rintro ⟨d,hd,he⟩
        exact (Sym2.map.injective source.input.qR_injective he) ▸ hd
      · intro h
        exact ⟨_,h,rfl⟩
    simp [actualRightRow,ground,labelEdge,GraphData.rows,Finset.mem_image,hp]
/-- The terminal row agrees with ANY original right chord having this physical
terminal pair. This asserts no uniqueness of its index. Reversed orientation
is handled by reversing the actual right path. -/
theorem terminal_row_of_chord (c : source.right.chords)
    (hc : s(source.right.start c,source.right.finish c) = s(source.aR,source.bR)) :
    source.terminalRow = source.right.rows.row c := by
  rcases Sym2.eq_iff.mp hc with ⟨hs,hf⟩ | ⟨hs,hf⟩
  · have hpath := source.right.path_eq c
      ((source.input.rightPath source.aR source.bR).copy hs.symm hf.symm)
      (by simpa only [SimpleGraph.Walk.isPath_copy] using
        CutTree.treePath_isPath source.right.isTree source.aR source.bR)
    ext j
    simp only [terminalRow, GraphData.rows, Finset.mem_filter]
    rw [hpath,SimpleGraph.Walk.edges_copy]
  · have hpath := source.right.path_eq c
      ((source.input.rightPath source.aR source.bR).reverse.copy hs.symm hf.symm)
      (by simpa only [SimpleGraph.Walk.isPath_copy] using
        (CutTree.treePath_isPath source.right.isTree source.aR source.bR).reverse)
    ext j
    simp only [terminalRow, GraphData.rows, Finset.mem_filter]
    rw [hpath,SimpleGraph.Walk.edges_copy,SimpleGraph.Walk.edges_reverse,List.mem_reverse]

/-- The original indexed-row substitution prerequisite, even when the marked
physical right chord has several indices. Index deletion/root reconstruction
remains G1B, and is not inferred from this equation. -/
theorem left_row_of_interface (c : source.left.chords) (r : source.right.chords)
    (hr : s(source.right.start r,source.right.finish r) = s(source.aR,source.bR)) :
    source.actualLeftRow c =
      ((source.left.rows.row c).erase source.e).image Sum.inl ∪
      (if source.e ∈ source.left.rows.row c then
        (source.right.rows.row r).image Sum.inr else ∅) := by
  rw [source.left_row_substitution,source.terminal_row_of_chord r hr]
end GraphSource
end D5.S3.Geometry.OriginalLabelTwoSum
