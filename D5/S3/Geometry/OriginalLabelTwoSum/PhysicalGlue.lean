/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue
   mirror-E: none(waiver:original-label-physical-glue)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Actual physical edge two-sum GraphData and path-derived rows on the unchanged ambient labels. -/
import D5.S3.Geometry.OriginalLabelTwoSum.CutGraphRows
import D5.S3.Geometry.OriginalLabelTwoSum.InterfaceNormalization

/-! SOURCE ONLY, UNCOMPILED. Original input graphs are the only graph data
assumed. The parent graph, its tree, labels, chord soundness/coverage and rows
are constructed below. The actual tree theorem is the released CutTree theorem;
the row theorem consumes its actual oriented path substitution. -/
noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum

/-- A retained left tree edge and an actual right chord in the SAME ambient
label type. No parent graph, path, row or root is a field. -/
structure PhysicalGlue (VL VR Label : Type*) [Fintype Label] [DecidableEq Label] where
  left : GraphData VL Label
  right : GraphData VR Label
  selected : right.chords
  X Y : Finset Label
  e : Label
  left_ground : left.ground = insert e X
  right_ground : right.ground = Y
  e_not_X : e ∉ X
  e_not_Y : e ∉ Y
  disjoint : Disjoint X Y
  aL bL : VL
  edge_e : left.edge e = s(aL,bL)

namespace PhysicalGlue
variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]
  (g : PhysicalGlue VL VR Label)

theorem selected_mem : g.e ∈ g.left.ground := by simp [g.left_ground]

/-- Right terminal distinctness is derived from chord soundness. -/
def source : GraphSource VL VR Label Label where
  left := g.left
  right := g.right
  aL := g.aL
  bL := g.bL
  aR := g.right.start g.selected
  bR := g.right.finish g.selected
  htermR := (g.right.chord_adj g.selected).ne
  e := g.e
  he := g.selected_mem
  edge_e := g.edge_e

abbrev input := g.source.input
abbrev Carrier := g.input.Carrier
abbrev qL := g.input.qL
abbrev qR := g.input.qR
abbrev leftKept := g.left.graph.deleteEdges {g.left.edge g.e}
abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

/-- Delete BOTH physical interfaces before taking the edge-image union. -/
def graph : SimpleGraph g.Carrier :=
  g.leftKept.map g.input.leftEmbedding ⊔ g.rightKept.map g.input.rightEmbedding

theorem graph_adjacency (w z : g.Carrier) : g.graph.Adj w z ↔
    (∃ x y, g.leftKept.Adj x y ∧ g.qL x = w ∧ g.qL y = z) ∨
    (∃ x y, g.rightKept.Adj x y ∧ g.qR x = w ∧ g.qR y = z) := by
  simp only [graph, SimpleGraph.sup_adj, SimpleGraph.map_adj]

theorem graph_edgeSet : g.graph.edgeSet =
    Sym2.map g.qL '' g.leftKept.edgeSet ∪
      Sym2.map g.qR '' g.rightKept.edgeSet := by
  simpa only [graph, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map]

private theorem adj_of_pair_eq {V : Type*} (G : SimpleGraph V)
    {x y a b : V} (h : G.Adj x y) (he : s(x,y) = s(a,b)) : G.Adj a b := by
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact h
  · exact h.symm

/-- A nonloop collision between the two images is exactly the terminal pair.
This includes reversed endpoints and says nothing about ghost-label loops. -/
theorem cross_pair {x y : VL} {u v : VR} (hne : x ≠ y)
    (he : Sym2.map g.qL s(x,y) = Sym2.map g.qR s(u,v)) :
    s(x,y) = s(g.aL,g.bL) ∧ s(u,v) = g.right.kappa g.selected := by
  have aligned : ∀ u v, g.qL x = g.qR u → g.qL y = g.qR v →
      s(x,y) = s(g.aL,g.bL) ∧ s(u,v) = g.right.kappa g.selected := by
    intro u v hx hy
    rcases (g.input.overlap x u).mp hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases (g.input.overlap y v).mp hy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact False.elim (hne rfl)
    · exact ⟨rfl,rfl⟩
    · exact ⟨Sym2.eq_swap,Sym2.eq_swap⟩
    · exact False.elim (hne rfl)
  simp only [Sym2.map_mk, Sym2.eq_iff] at he
  rcases he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact aligned u v hx hy
  · obtain ⟨hL,hR⟩ := aligned v u hx hy
    exact ⟨hL,Sym2.eq_swap.trans hR⟩

/-- The retained physical graph images are disjoint, including arbitrary
duplicate chord indices on other physical edges. -/
theorem graph_images_disjoint :
    Disjoint (Sym2.map g.qL '' g.leftKept.edgeSet)
      (Sym2.map g.qR '' g.rightKept.edgeSet) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨d,hd,rfl⟩ ⟨f,hf,he⟩
  induction d using Sym2.ind with
  | h x y =>
    induction f using Sym2.ind with
    | h u v =>
      have hl := SimpleGraph.deleteEdges_adj.mp hd
      have hc := g.cross_pair hl.1.ne he.symm
      exact hl.2 (by simpa [g.edge_e] using hc.1)

theorem graph_left (x y : VL) :
    g.graph.Adj (g.qL x) (g.qL y) ↔ g.leftKept.Adj x y := by
  rw [g.graph_adjacency]
  constructor
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · have hux := g.input.qL_injective hu
      have hvy := g.input.qL_injective hv
      simpa only [hux,hvy] using h
    · have hr := SimpleGraph.deleteEdges_adj.mp h
      have hne : x ≠ y := by
        intro hxy
        apply hr.1.ne
        apply g.input.qR_injective
        exact hu.trans ((congrArg g.qL hxy).trans hv.symm)
      have he : Sym2.map g.qL s(x,y) = Sym2.map g.qR s(u,v) := by
        simp only [Sym2.map_mk,hu,hv]
      exact False.elim (hr.2 (by simpa using (g.cross_pair hne he).2))
  · intro h
    exact Or.inl ⟨x,y,h,rfl,rfl⟩

theorem graph_right (x y : VR) :
    g.graph.Adj (g.qR x) (g.qR y) ↔ g.rightKept.Adj x y := by
  rw [g.graph_adjacency]
  constructor
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · have hl := SimpleGraph.deleteEdges_adj.mp h
      have he : Sym2.map g.qL s(u,v) = Sym2.map g.qR s(x,y) := by
        simp only [Sym2.map_mk,hu,hv]
      exact False.elim (hl.2 (by simpa [g.edge_e] using (g.cross_pair hl.1.ne he).1))
    · have hux := g.input.qR_injective hu
      have hvy := g.input.qR_injective hv
      simpa only [hux,hvy] using h
  · intro h
    exact Or.inr ⟨x,y,h,rfl,rfl⟩

theorem tree_left (x y : VL) :
    g.input.tree.Adj (g.qL x) (g.qL y) ↔ g.input.cut.Adj x y := by
  have hn : ¬g.input.TR.Adj g.input.aR g.input.bR :=
    g.right.chord_not_tree g.selected
  simpa only [hn,false_and,or_false] using g.input.adjacency_left x y

theorem tree_le : g.input.tree ≤ g.graph := by
  intro w z h
  rcases (g.input.adjacency w z).mp h with ⟨x,y,hl,rfl,rfl⟩ | ⟨x,y,hr,rfl,rfl⟩
  · apply (g.graph_left x y).mpr
    have hd := SimpleGraph.deleteEdges_adj.mp hl
    apply SimpleGraph.deleteEdges_adj.mpr
    exact ⟨g.left.tree_le hd.1,by simpa [g.edge_e] using hd.2⟩
  · apply (g.graph_right x y).mpr
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨g.right.tree_le hr,?_⟩
    intro he
    have hp : s(x,y) = g.right.kappa g.selected := by simpa using he
    exact g.right.chord_not_tree g.selected (adj_of_pair_eq g.right.tree hr hp)

/-- TOTAL label function, including e and every nonground ambient label. -/
def labelEdge (i : Label) : Sym2 g.Carrier :=
  if i ∈ g.Y then Sym2.map g.qR (g.right.edge i)
  else Sym2.map g.qL (g.left.edge i)

theorem label_left {i : Label} (hi : i ∈ g.X) :
    g.labelEdge i = Sym2.map g.qL (g.left.edge i) := by
  have hn : i ∉ g.Y := fun h => Finset.disjoint_left.mp g.disjoint hi h
  simp only [labelEdge,if_neg hn]

theorem label_right {i : Label} (hi : i ∈ g.Y) :
    g.labelEdge i = Sym2.map g.qR (g.right.edge i) := by
  simp only [labelEdge,if_pos hi]

private theorem labelled_mem {V : Type*} (s : GraphData V Label)
    {i : Label} (hi : i ∈ s.ground) : s.edge i ∈ s.tree.edgeSet := by
  have h : ∀ d : Sym2 V, s.edge i = d → d ∈ s.tree.edgeSet := by
    apply Sym2.ind
    intro x y he
    exact (s.tree_edges x y).mpr ⟨i,hi,he⟩
  exact h _ rfl

theorem retained_label_mem {i : Label} (hi : i ∈ g.X) :
    g.left.edge i ∈ g.input.cut.edgeSet := by
  have hgi : i ∈ g.left.ground := by rw [g.left_ground]; exact Finset.mem_insert_of_mem hi
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨labelled_mem g.left hgi,?_⟩
  intro he
  have he' : g.left.edge i = g.left.edge g.e := by simpa [g.edge_e] using he
  have hie := g.left.labels_injective i hgi g.e g.selected_mem he'
  exact g.e_not_X (hie ▸ hi)

theorem active_label_mem {i : Label} (hi : i ∈ g.X ∪ g.Y) :
    g.labelEdge i ∈ g.input.tree.edgeSet := by
  rw [g.input.edgeSet]
  rcases Finset.mem_union.mp hi with hx | hy
  · rw [g.label_left hx]
    exact Or.inl ⟨g.left.edge i,g.retained_label_mem hx,rfl⟩
  · rw [g.label_right hy]
    exact Or.inr ⟨g.right.edge i,labelled_mem g.right (g.right_ground.symm ▸ hy),rfl⟩

theorem tree_edges (w z : g.Carrier) :
    g.input.tree.Adj w z ↔ ∃ i ∈ g.X ∪ g.Y, g.labelEdge i = s(w,z) := by
  constructor
  · intro h
    rcases (g.input.adjacency w z).mp h with ⟨x,y,hl,rfl,rfl⟩ | ⟨x,y,hr,rfl,rfl⟩
    · have hd := SimpleGraph.deleteEdges_adj.mp hl
      obtain ⟨i,hi,hei⟩ := (g.left.tree_edges x y).mp hd.1
      have hne : i ≠ g.e := by
        intro he
        subst i
        exact hd.2 (by simp only [← hei,g.edge_e,Set.mem_singleton_iff])
      have hx : i ∈ g.X := by
        rw [g.left_ground] at hi
        exact (Finset.mem_insert.mp hi).resolve_left hne
      refine ⟨i,Finset.mem_union_left _ hx,?_⟩
      rw [g.label_left hx,hei]
      rfl
    · obtain ⟨i,hi,hei⟩ := (g.right.tree_edges x y).mp hr
      have hy : i ∈ g.Y := g.right_ground ▸ hi
      refine ⟨i,Finset.mem_union_right _ hy,?_⟩
      rw [g.label_right hy,hei]
      rfl
  · rintro ⟨i,hi,he⟩
    have hm := g.active_label_mem hi
    rw [he] at hm
    exact hm

theorem labels_injective (i : Label) (hi : i ∈ g.X ∪ g.Y)
    (j : Label) (hj : j ∈ g.X ∪ g.Y) (he : g.labelEdge i = g.labelEdge j) : i = j := by
  rcases Finset.mem_union.mp hi with hi | hi <;>
    rcases Finset.mem_union.mp hj with hj | hj
  · rw [g.label_left hi,g.label_left hj] at he
    apply g.left.labels_injective i (by rw [g.left_ground]; exact Finset.mem_insert_of_mem hi)
      j (by rw [g.left_ground]; exact Finset.mem_insert_of_mem hj)
    exact Sym2.map.injective g.input.qL_injective he
  · rw [g.label_left hi,g.label_right hj] at he
    exact False.elim (Set.disjoint_left.mp g.input.edge_images_disjoint
      ⟨g.left.edge i,g.retained_label_mem hi,rfl⟩
      ⟨g.right.edge j,labelled_mem g.right (g.right_ground.symm ▸ hj),he.symm⟩)
  · rw [g.label_right hi,g.label_left hj] at he
    exact False.elim (Set.disjoint_left.mp g.input.edge_images_disjoint
      ⟨g.left.edge j,g.retained_label_mem hj,rfl⟩
      ⟨g.right.edge i,labelled_mem g.right (g.right_ground.symm ▸ hi),he⟩)
  · rw [g.label_right hi,g.label_right hj] at he
    exact g.right.labels_injective i (g.right_ground.symm ▸ hi)
      j (g.right_ground.symm ▸ hj) (Sym2.map.injective g.input.qR_injective he)

abbrev Chords := g.left.chords ⊕ g.right.PhysicalSurvivor g.selected

def start : g.Chords → g.Carrier
  | .inl c => g.qL (g.left.start c)
  | .inr d => g.qR (g.right.start d.1)

def finish : g.Chords → g.Carrier
  | .inl c => g.qL (g.left.finish c)
  | .inr d => g.qR (g.right.finish d.1)

theorem chord_adj (c : g.Chords) : g.graph.Adj (g.start c) (g.finish c) := by
  cases c with
  | inl c =>
    apply (g.graph_left _ _).mpr
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨g.left.chord_adj c,?_⟩
    intro he
    have hp : s(g.left.start c,g.left.finish c) = g.left.edge g.e := by simpa using he
    exact g.left.chord_not_tree c (adj_of_pair_eq g.left.tree g.source.terminal_adj
      (g.edge_e.symm.trans hp.symm))
  | inr d =>
    apply (g.graph_right _ _).mpr
    exact SimpleGraph.deleteEdges_adj.mpr ⟨g.right.chord_adj d.1,by simpa using d.2⟩

theorem chord_not_tree (c : g.Chords) :
    ¬g.input.tree.Adj (g.start c) (g.finish c) := by
  cases c with
  | inl c =>
    intro h
    exact g.left.chord_not_tree c
      ((SimpleGraph.deleteEdges_le _) ((g.tree_left _ _).mp h))
  | inr d =>
    intro h
    exact g.right.chord_not_tree d.1 ((g.input.adjacency_right _ _).mp h)

theorem chord_cover (w z : g.Carrier) (h : g.graph.Adj w z)
    (hn : ¬g.input.tree.Adj w z) : ∃ c : g.Chords, s(g.start c,g.finish c) = s(w,z) := by
  rcases (g.graph_adjacency w z).mp h with ⟨x,y,hl,rfl,rfl⟩ | ⟨x,y,hr,rfl,rfl⟩
  · have hd := SimpleGraph.deleteEdges_adj.mp hl
    have hnt : ¬g.left.tree.Adj x y := by
      intro ht
      apply hn
      apply (g.tree_left x y).mpr
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨ht,by simpa [g.edge_e] using hd.2⟩
    obtain ⟨c,hc⟩ := g.left.chord_cover x y hd.1 hnt
    exact ⟨.inl c,congrArg (Sym2.map g.qL) hc⟩
  · have hd := SimpleGraph.deleteEdges_adj.mp hr
    have hnt : ¬g.right.tree.Adj x y := fun ht =>
      hn ((g.input.adjacency_right x y).mpr ht)
    obtain ⟨d,hd'⟩ := g.right.chord_cover x y hd.1 hnt
    have hs : g.right.kappa d ≠ g.right.kappa g.selected := by
      intro he
      exact hd.2 (by simpa only [Set.mem_singleton_iff] using hd'.symm.trans he)
    exact ⟨.inr ⟨d,hs⟩,congrArg (Sym2.map g.qR) hd'⟩

/-- Every field is constructed or proved. In particular tree_le/isTree,
coverage, TOTAL edge and injection are not supplied by an input contract. -/
def data : GraphData g.Carrier Label where
  graph := g.graph
  tree := g.input.tree
  tree_le := g.tree_le
  isTree := g.source.actual_tree
  ground := g.X ∪ g.Y
  edge := g.labelEdge
  tree_edges := g.tree_edges
  labels_injective := g.labels_injective
  chords := g.Chords
  start := g.start
  finish := g.finish
  chord_adj := g.chord_adj
  chord_not_tree := g.chord_not_tree
  chord_cover := g.chord_cover

/-- Forget the internal G1A tags, after proving the original active supports
are disjoint. The public endpoint is a finset of original Label values. -/
private def forgetTag : Label ⊕ Label → Label := Sum.elim id id

private theorem erase_ground : g.left.ground.erase g.e = g.X := by
  rw [g.left_ground]
  exact Finset.erase_insert g.e_not_X

private theorem tagged_left (c : g.left.chords) :
    g.data.rows.row (.inl c) = (g.source.actualLeftRow c).image forgetTag := by
  classical
  ext i
  simp only [Finset.mem_image]
  change (i ∈ (g.X ∪ g.Y).filter (fun j => g.labelEdge j ∈
      (g.input.path (g.qL (g.left.start c)) (g.qL (g.left.finish c))).edges)) ↔ _
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi,hp⟩
    rcases Finset.mem_union.mp hi with hx | hy
    · refine ⟨.inl i,?_,rfl⟩
      change Sum.inl i ∈ g.source.ground.filter _
      simp only [Finset.mem_filter]
      refine ⟨?_,?_⟩
      · simp [GraphSource.ground,g.erase_ground,Finset.mem_image,hx]
      · change Sym2.map g.qL (g.left.edge i) ∈ _
        rwa [g.label_left hx] at hp
    · refine ⟨.inr i,?_,rfl⟩
      change Sum.inr i ∈ g.source.ground.filter _
      simp only [Finset.mem_filter]
      refine ⟨?_,?_⟩
      · simp [GraphSource.ground,g.right_ground,Finset.mem_image,hy]
      · change Sym2.map g.qR (g.right.edge i) ∈ _
        rwa [g.label_right hy] at hp
  · rintro ⟨j,hj,he⟩
    cases j with
    | inl j =>
      change j = i at he
      subst j
      change Sum.inl i ∈ g.source.ground.filter _ at hj
      simp only [Finset.mem_filter] at hj
      have hx : i ∈ g.X := by
        simpa [GraphSource.ground,g.erase_ground,Finset.mem_image] using hj.1
      exact ⟨Finset.mem_union_left _ hx,by rw [g.label_left hx]; exact hj.2⟩
    | inr j =>
      change j = i at he
      subst j
      change Sum.inr i ∈ g.source.ground.filter _ at hj
      simp only [Finset.mem_filter] at hj
      have hy : i ∈ g.Y := by
        simpa [GraphSource.ground,g.right_ground,Finset.mem_image] using hj.1
      exact ⟨Finset.mem_union_right _ hy,by rw [g.label_right hy]; exact hj.2⟩

private theorem tagged_right (d : g.right.PhysicalSurvivor g.selected) :
    g.data.rows.row (.inr d) = (g.source.actualRightRow d.1).image forgetTag := by
  classical
  ext i
  simp only [Finset.mem_image]
  change (i ∈ (g.X ∪ g.Y).filter (fun j => g.labelEdge j ∈
      (g.input.path (g.qR (g.right.start d.1)) (g.qR (g.right.finish d.1))).edges)) ↔ _
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi,hp⟩
    rcases Finset.mem_union.mp hi with hx | hy
    · refine ⟨.inl i,?_,rfl⟩
      change Sum.inl i ∈ g.source.ground.filter _
      simp only [Finset.mem_filter]
      refine ⟨?_,?_⟩
      · simp [GraphSource.ground,g.erase_ground,Finset.mem_image,hx]
      · change Sym2.map g.qL (g.left.edge i) ∈ _
        rwa [g.label_left hx] at hp
    · refine ⟨.inr i,?_,rfl⟩
      change Sum.inr i ∈ g.source.ground.filter _
      simp only [Finset.mem_filter]
      refine ⟨?_,?_⟩
      · simp [GraphSource.ground,g.right_ground,Finset.mem_image,hy]
      · change Sym2.map g.qR (g.right.edge i) ∈ _
        rwa [g.label_right hy] at hp
  · rintro ⟨j,hj,he⟩
    cases j with
    | inl j =>
      change j = i at he
      subst j
      change Sum.inl i ∈ g.source.ground.filter _ at hj
      simp only [Finset.mem_filter] at hj
      have hx : i ∈ g.X := by
        simpa [GraphSource.ground,g.erase_ground,Finset.mem_image] using hj.1
      exact ⟨Finset.mem_union_left _ hx,by rw [g.label_left hx]; exact hj.2⟩
    | inr j =>
      change j = i at he
      subst j
      change Sum.inr i ∈ g.source.ground.filter _ at hj
      simp only [Finset.mem_filter] at hj
      have hy : i ∈ g.Y := by
        simpa [GraphSource.ground,g.right_ground,Finset.mem_image] using hj.1
      exact ⟨Finset.mem_union_right _ hy,by rw [g.label_right hy]; exact hj.2⟩

/-- Actual path-derived left rows, on the SAME ambient labels. G1A handles
both orientations, zero-length path segments and duplicate original indices. -/
theorem left_row (c : g.left.chords) :
    g.data.rows.row (.inl c) = substitute g.e (g.right.rows.row g.selected) (g.left.rows.row c) := by
  classical
  rw [g.tagged_left, g.source.left_row_of_interface c g.selected rfl]
  by_cases he : g.e ∈ g.left.rows.row c
  · simp [substitute,he,forgetTag,Finset.image_image]
  · simp [substitute,he,forgetTag,Finset.image_image,Finset.erase_eq_of_not_mem he]

theorem right_row (d : g.right.PhysicalSurvivor g.selected) :
    g.data.rows.row (.inr d) = g.right.rows.row d.1 := by
  classical
  rw [g.tagged_right, g.source.right_row_inheritance d.1,Finset.image_image]
  change (g.right.rows.row d.1).image id = _
  exact Finset.image_id

/-- Exact identity of the original index families. No chord is reindexed by a
quotient, and no assumption about parent rows occurs in the telescope. -/
theorem row_family (c : g.data.chords) : g.data.rows.row c =
    (physicalTransportedRows g.X g.Y g.e g.left.rows g.right g.selected
      g.left_ground g.right_ground g.e_not_X g.e_not_Y).row c := by
  cases c with
  | inl c => exact g.left_row c
  | inr d => exact g.right_row d

theorem root_agreement : g.data.rows.root =
    (physicalTransportedRows g.X g.Y g.e g.left.rows g.right g.selected
      g.left_ground g.right_ground g.e_not_X g.e_not_Y).root := by
  apply SetLike.ext
  intro s
  change (∃ c : g.data.chords, s ⊆ (g.X ∪ g.Y) \ g.data.rows.row c) ↔ _
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c,by rwa [g.row_family c] at hc⟩
  · rintro ⟨c,hc⟩
    exact ⟨c,by rwa [← g.row_family c] at hc⟩

/-- Unconditional corrected actual-graph raw root, including VOID/UNIT and
every retained ground label. No desired graph/root equation is an input. -/
theorem root_formula : g.data.rows.root =
    phi g.X g.Y (g.Y \ g.right.rows.row g.selected) (restrict g.X g.left.rows.root)
      (rawLink g.X g.e g.left.rows.root) (g.right.E_edge g.selected) := by
  rw [g.root_agreement]
  exact physical_row_transport g.X g.Y g.e g.left.rows g.right g.selected
    g.left_ground g.right_ground g.e_not_X g.e_not_Y g.disjoint

/-- Local U* corollary. U* is not asserted necessary for accidental face-set
equality, and imposes no uniqueness on any other physical chord fiber. -/
theorem root_formula_of_unique (hu : g.right.UniqueInterface g.selected) :
    g.data.rows.root =
      phi g.X g.Y (g.Y \ g.right.rows.row g.selected) (restrict g.X g.left.rows.root)
        (rawLink g.X g.e g.left.rows.root) (g.right.rows.without g.selected).root := by
  rw [g.root_formula,g.right.E_edge_eq_without g.selected hu]

/-- Literal survivor-index equivalence under U*, identity on each original
right index and every left index. It does not identify duplicate other chords. -/
def uniqueChordEquiv (hu : g.right.UniqueInterface g.selected) :
    g.data.chords ≃ g.left.chords ⊕ {d : g.right.chords // d ≠ g.selected} :=
  Equiv.sumCongr (Equiv.refl _) {
    toFun := fun d => ⟨d.1,fun he => d.2 (congrArg g.right.kappa he)⟩
    invFun := fun d => ⟨d.1,fun he => d.2 (hu d.1 he)⟩
    left_inv := fun d => by apply Subtype.ext; rfl
    right_inv := fun d => by apply Subtype.ext; rfl }

theorem unique_row (hu : g.right.UniqueInterface g.selected) (c : g.data.chords) :
    g.data.rows.row c =
      (transportedRows g.X g.Y g.e (g.right.rows.row g.selected) g.left.rows g.right.rows
        g.selected g.left_ground g.right_ground g.e_not_X g.e_not_Y
        (g.right_ground ▸ g.right.rows.row_supported g.selected)).row
          (g.uniqueChordEquiv hu c) := by
  cases c with
  | inl c => exact g.left_row c
  | inr d => exact g.right_row d

theorem literal_root_agreement (hu : g.right.UniqueInterface g.selected) :
    g.data.rows.root =
      (transportedRows g.X g.Y g.e (g.right.rows.row g.selected) g.left.rows g.right.rows
        g.selected g.left_ground g.right_ground g.e_not_X g.e_not_Y
        (g.right_ground ▸ g.right.rows.row_supported g.selected)).root := by
  exact (g.root_formula_of_unique hu).trans
    (row_transport g.X g.Y g.e (g.right.rows.row g.selected) g.left.rows g.right.rows
      g.selected g.left_ground g.right_ground g.e_not_X g.e_not_Y g.disjoint
      (g.right_ground ▸ g.right.rows.row_supported g.selected) rfl).symm

end PhysicalGlue

end D5.S3.Geometry.OriginalLabelTwoSum
