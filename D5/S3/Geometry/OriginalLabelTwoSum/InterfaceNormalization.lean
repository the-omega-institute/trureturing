/- GID: D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization
   mirror-E: none(waiver:original-label-interface-normalization)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Physical interface deletion retains original noninterface indices and is reduced to the existing raw row transport by path-derived interface normalization. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Graph

/-! SOURCE ONLY, UNCOMPILED. T06 of the corrected ordinary proof is the
mathematical specification. No finite vertex or chord-index assumption is used.
`labels_injective` is never used as chord-index injectivity. The actual glued
graph and its path substitution theorem (G1A) are separate pending inputs to a
later graph-bound consumer, not hypotheses of the raw formula proved here. -/
noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum

namespace GraphData
variable {Vertex Label : Type*} [Fintype Label] [DecidableEq Label]

/-- The physical unordered edge of an original chord index. -/
def kappa (g : GraphData Vertex Label) (d : g.chords) : Sym2 Vertex :=
  s(g.start d,g.finish d)

/-- Original physical survivor indices, without quotienting any other fiber. -/
def PhysicalSurvivor (g : GraphData Vertex Label) (c : g.chords) :=
  {d : g.chords // g.kappa d ≠ g.kappa c}

/-- Restrict exactly the index type; ground, labels and rows stay original. -/
def physicalRows (g : GraphData Vertex Label) (c : g.chords) : Rows Label where
  ground := g.ground
  chords := g.PhysicalSurvivor c
  row d := g.rows.row d.1
  row_supported d := g.rows.row_supported d.1

/-- The unrestricted physical-edge deletion root in the existing raw Family. -/
def E_edge (g : GraphData Vertex Label) (c : g.chords) : Family Label :=
  (g.physicalRows c).root

/-- Local U*: uniqueness only over the selected interface, never globally. -/
def UniqueInterface (g : GraphData Vertex Label) (c : g.chords) : Prop :=
  ∀ d, g.kappa d = g.kappa c → d = c

private theorem selectedPath_isPath (g : GraphData Vertex Label) (d : g.chords) :
    (g.path d).IsPath :=
  (Classical.choose_spec (g.isTree.existsUnique_path (g.start d) (g.finish d))).1

private theorem treePath_edge_membership {T : SimpleGraph Vertex} (hT : T.IsTree)
    {a b x y : Vertex} (p : T.Walk a b) (hp : p.IsPath)
    (q : T.Walk x y) (hq : q.IsPath) (h : s(a,b) = s(x,y))
    (z : Sym2 Vertex) : z ∈ p.edges ↔ z ∈ q.edges := by
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have heq : q = p.copy ha hb :=
      (hT.existsUnique_path x y).unique hq ((p.isPath_copy ha hb).mpr hp)
    rw [heq, SimpleGraph.Walk.edges_copy]
  · have heq : q = p.reverse.copy hb ha :=
      (hT.existsUnique_path x y).unique hq
        ((p.reverse.isPath_copy hb ha).mpr hp.reverse)
    rw [heq, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse]

/-- Equal physical chords have equal actual path-derived rows, including the
reversed orientation. This follows from tree path uniqueness, not an input. -/
theorem rows_eq_of_kappa_eq (g : GraphData Vertex Label) (d c : g.chords)
    (h : g.kappa d = g.kappa c) : g.rows.row d = g.rows.row c := by
  classical
  apply Finset.ext
  intro i
  change (i ∈ g.ground.filter (fun i => g.edge i ∈ (g.path d).edges)) ↔
    (i ∈ g.ground.filter (fun i => g.edge i ∈ (g.path c).edges))
  simp only [Finset.mem_filter]
  exact and_congr Iff.rfl (treePath_edge_membership g.isTree
    (g.path d) (selectedPath_isPath g d) (g.path c) (selectedPath_isPath g c)
    h (g.edge i))

/-- Normalize only the interface fiber: retain c and every noninterface
original index. Every other GraphData field is literally inherited. -/
def normalizeInterface (g : GraphData Vertex Label) (c : g.chords) :
    GraphData Vertex Label where
  graph := g.graph
  tree := g.tree
  tree_le := g.tree_le
  isTree := g.isTree
  ground := g.ground
  edge := g.edge
  tree_edges := g.tree_edges
  labels_injective := g.labels_injective
  chords := {d : g.chords // d = c ∨ g.kappa d ≠ g.kappa c}
  start d := g.start d.1
  finish d := g.finish d.1
  chord_adj d := g.chord_adj d.1
  chord_not_tree d := g.chord_not_tree d.1
  chord_cover := by
    classical
    intro x y hxy hnt
    obtain ⟨d,hd⟩ := g.chord_cover x y hxy hnt
    by_cases hi : g.kappa d = g.kappa c
    · exact ⟨⟨c,Or.inl rfl⟩,hi.symm.trans hd⟩
    · exact ⟨⟨d,Or.inr hi⟩,hd⟩

/-- The retained distinguished index is c itself, with subtype evidence. -/
def normalizedChord (g : GraphData Vertex Label) (c : g.chords) :
    (g.normalizeInterface c).chords := ⟨c,Or.inl rfl⟩

/-- Normalization changes no row at any retained original index. -/
theorem normalized_row (g : GraphData Vertex Label) (c : g.chords)
    (d : (g.normalizeInterface c).chords) :
    (g.normalizeInterface c).rows.row d = g.rows.row d.1 := by
  classical
  have hp : g.path d.1 = (g.normalizeInterface c).path d :=
    g.path_eq d.1 _ (selectedPath_isPath (g.normalizeInterface c) d)
  change g.ground.filter (fun i => g.edge i ∈ ((g.normalizeInterface c).path d).edges) =
    g.ground.filter (fun i => g.edge i ∈ (g.path d.1).edges)
  rw [hp]

/-- The interface's actual path row is preserved. -/
theorem normalized_distinguished_row (g : GraphData Vertex Label) (c : g.chords) :
    (g.normalizeInterface c).rows.row (g.normalizedChord c) = g.rows.row c :=
  g.normalized_row c (g.normalizedChord c)

/-- The complete raw root is unchanged, including empty-face membership. -/
theorem normalized_root (g : GraphData Vertex Label) (c : g.chords) :
    (g.normalizeInterface c).rows.root = g.rows.root := by
  classical
  apply SetLike.ext
  intro s
  change (∃ d : (g.normalizeInterface c).chords,
    s ⊆ g.ground \ (g.normalizeInterface c).rows.row d) ↔
    ∃ d : g.chords, s ⊆ g.ground \ g.rows.row d
  constructor
  · rintro ⟨d,hs⟩
    exact ⟨d.1, by rwa [g.normalized_row c d] at hs⟩
  · rintro ⟨d,hs⟩
    by_cases hi : g.kappa d = g.kappa c
    · refine ⟨g.normalizedChord c,?_⟩
      rw [g.normalized_distinguished_row c, ← g.rows_eq_of_kappa_eq d c hi]
      exact hs
    · exact ⟨⟨d,Or.inr hi⟩,by rwa [g.normalized_row c ⟨d,Or.inr hi⟩]⟩

/-- The normalized presentation has U*, with no restriction on other fibers. -/
theorem normalized_uniqueInterface (g : GraphData Vertex Label) (c : g.chords) :
    (g.normalizeInterface c).UniqueInterface (g.normalizedChord c) := by
  intro d hd
  apply Subtype.ext
  exact d.2.resolve_right (fun hn => hn hd)

/-- U* is exactly the survivor-index identification. No necessity assertion
about accidental equalities of raw face sets is made. -/
theorem uniqueInterface_iff_survivor_indices (g : GraphData Vertex Label)
    (c : g.chords) : g.UniqueInterface c ↔
      ∀ d, (g.kappa d ≠ g.kappa c ↔ d ≠ c) := by
  classical
  constructor
  · intro hu d
    constructor
    · intro hn he; exact hn (congrArg g.kappa he)
    · intro hn he; exact hn (hu d he)
  · intro hs d he
    by_contra hn
    exact ((hs d).mpr hn) he

/-- Explicit local COROLLARY: physical deletion is one-index deletion under U*. -/
theorem E_edge_eq_without (g : GraphData Vertex Label) (c : g.chords)
    (hu : g.UniqueInterface c) : g.E_edge c = (g.rows.without c).root := by
  have hs := (g.uniqueInterface_iff_survivor_indices c).mp hu
  apply SetLike.ext
  intro s
  change (∃ d : g.PhysicalSurvivor c, s ⊆ g.ground \ g.rows.row d.1) ↔
    ∃ d : {d : g.chords // d ≠ c}, s ⊆ g.ground \ g.rows.row d.1
  constructor
  · rintro ⟨d,hd⟩; exact ⟨⟨d.1,(hs d.1).mp d.2⟩,hd⟩
  · rintro ⟨d,hd⟩; exact ⟨⟨d.1,(hs d.1).mpr d.2⟩,hd⟩

/-- Canonical identity-on-original-indices equivalence after normalized deletion.
In particular, duplicate noninterface indices remain distinct. -/
def normalizedSurvivorEquiv (g : GraphData Vertex Label) (c : g.chords) :
    {d : (g.normalizeInterface c).chords // d ≠ g.normalizedChord c} ≃
      g.PhysicalSurvivor c where
  toFun d := ⟨d.1.1, by
    intro he
    exact d.2 (g.normalized_uniqueInterface c d.1 he)⟩
  invFun d := ⟨⟨d.1,Or.inr d.2⟩,by
    intro he
    exact d.2 (congrArg g.kappa (congrArg Subtype.val he))⟩
  left_inv d := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; rfl

/-- The normalized one-index deletion is precisely E_edge on the same ground. -/
theorem normalized_without_root (g : GraphData Vertex Label) (c : g.chords) :
    ((g.normalizeInterface c).rows.without (g.normalizedChord c)).root =
      g.E_edge c := by
  apply SetLike.ext
  intro s
  change (∃ d : {d : (g.normalizeInterface c).chords // d ≠ g.normalizedChord c},
    s ⊆ g.ground \ (g.normalizeInterface c).rows.row d.1) ↔
    ∃ d : g.PhysicalSurvivor c, s ⊆ g.ground \ g.rows.row d.1
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨g.normalizedSurvivorEquiv c d,?_⟩
    rw [g.normalized_row c d.1] at hd
    exact hd
  · rintro ⟨d,hd⟩
    refine ⟨(g.normalizedSurvivorEquiv c).symm d,?_⟩
    rw [g.normalized_row c ((g.normalizedSurvivorEquiv c).symm d).1]
    exact hd

end GraphData

variable {Vertex Label : Type*} [Fintype Label] [DecidableEq Label]

/-- Literal corrected row presentation, indexed by old left chords and every
original physical right survivor. Its right rows are original actual path rows. -/
def physicalTransportedRows (X Y : Finset Label) (e : Label)
    (left : Rows Label) (g : GraphData Vertex Label) (c : g.chords)
    (hleft : left.ground = insert e X) (hright : g.ground = Y)
    (heX : e ∉ X) (heY : e ∉ Y) : Rows Label where
  ground := X ∪ Y
  chords := left.chords ⊕ g.PhysicalSurvivor c
  row
    | .inl d => substitute e (g.rows.row c) (left.row d)
    | .inr d => g.rows.row d.1
  row_supported := by
    intro d
    cases d with
    | inl d =>
      exact (transportedRows X Y e (g.rows.row c) left g.rows c hleft hright
        heX heY (hright ▸ g.rows.row_supported c)).row_supported (.inl d)
    | inr d =>
      exact fun i hi => Finset.mem_union_right _ (hright ▸ g.rows.row_supported d.1 hi)

/-- Both the full right input and the normalized transport output are faithful.
The second equality consumes the original row_transport, with the distinguished
path row preserved and the deleted-index term replaced by E_edge. -/
theorem normalized_row_transport (X Y : Finset Label) (e : Label)
    (left : Rows Label) (g : GraphData Vertex Label) (c : g.chords)
    (hleft : left.ground = insert e X) (hright : g.ground = Y)
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y) :
    ((g.normalizeInterface c).rows.root,
      (transportedRows X Y e (g.rows.row c) left (g.normalizeInterface c).rows
        (g.normalizedChord c) hleft hright heX heY
        (hright ▸ g.rows.row_supported c)).root) =
    (g.rows.root, phi X Y (Y \ g.rows.row c) (restrict X left.root)
      (rawLink X e left.root) (g.E_edge c)) := by
  apply Prod.ext
  · exact g.normalized_root c
  · have ht := row_transport X Y e (g.rows.row c) left (g.normalizeInterface c).rows
      (g.normalizedChord c) hleft hright heX heY hXY
      (hright ▸ g.rows.row_supported c) (g.normalized_distinguished_row c)
    rw [g.normalized_without_root c] at ht
    exact ht

/-- Unrestricted corrected row-algebra parent formula. There is no assumed
graph/root equation here. Binding the physical presentation to the actual glued
graph requires the independent G1A construction and path theorem. -/
theorem physical_row_transport (X Y : Finset Label) (e : Label)
    (left : Rows Label) (g : GraphData Vertex Label) (c : g.chords)
    (hleft : left.ground = insert e X) (hright : g.ground = Y)
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y) :
    (physicalTransportedRows X Y e left g c hleft hright heX heY).root =
      phi X Y (Y \ g.rows.row c) (restrict X left.root)
        (rawLink X e left.root) (g.E_edge c) := by
  have ht := congrArg Prod.snd
    (normalized_row_transport X Y e left g c hleft hright heX heY hXY)
  refine Eq.trans ?_ ht
  apply SetLike.ext
  intro s
  change (∃ d : left.chords ⊕ g.PhysicalSurvivor c,
      s ⊆ (X ∪ Y) \ (physicalTransportedRows X Y e left g c hleft hright heX heY).row d) ↔
    ∃ d : left.chords ⊕ {d : (g.normalizeInterface c).chords // d ≠ g.normalizedChord c},
      s ⊆ (X ∪ Y) \ (transportedRows X Y e (g.rows.row c) left
        (g.normalizeInterface c).rows (g.normalizedChord c) hleft hright heX heY
        (hright ▸ g.rows.row_supported c)).row d
  constructor
  · rintro ⟨d,hd⟩
    cases d with
    | inl d => exact ⟨Sum.inl d,hd⟩
    | inr d =>
      refine ⟨Sum.inr ((g.normalizedSurvivorEquiv c).symm d),?_⟩
      change s ⊆ (X ∪ Y) \ (g.normalizeInterface c).rows.row
        ((g.normalizedSurvivorEquiv c).symm d).1
      rw [g.normalized_row c ((g.normalizedSurvivorEquiv c).symm d).1]
      exact hd
  · rintro ⟨d,hd⟩
    cases d with
    | inl d => exact ⟨Sum.inl d,hd⟩
    | inr d =>
      refine ⟨Sum.inr (g.normalizedSurvivorEquiv c d),?_⟩
      change s ⊆ (X ∪ Y) \ (g.normalizeInterface c).rows.row d.1 at hd
      rw [g.normalized_row c d.1] at hd
      exact hd

/-- Local U* COROLLARY of the unrestricted formula; no global injectivity. -/
theorem physical_row_transport_of_unique (X Y : Finset Label) (e : Label)
    (left : Rows Label) (g : GraphData Vertex Label) (c : g.chords)
    (hleft : left.ground = insert e X) (hright : g.ground = Y)
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hu : g.UniqueInterface c) :
    (physicalTransportedRows X Y e left g c hleft hright heX heY).root =
      phi X Y (Y \ g.rows.row c) (restrict X left.root)
        (rawLink X e left.root) (g.rows.without c).root := by
  rw [← g.E_edge_eq_without c hu]
  exact physical_row_transport X Y e left g c hleft hright heX heY hXY

namespace CyclicInterface

/-- Successor around Fin m, written with an explicit wrap for arithmetic proofs. -/
def next {m : Nat} (hm : 3 ≤ m) (i : Fin m) : Fin m :=
  if h : i.val + 1 < m then ⟨i.val + 1,h⟩ else ⟨0,by omega⟩

/-- For every m>=3, cyclic unordered edges have unique indices. Reversed
endpoint matching would force a two-cycle, excluded by m>=3. -/
theorem cyclic_edge_injective {m : Nat} (hm : 3 ≤ m) :
    Function.Injective (fun i : Fin m => s(i,next hm i)) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with ⟨h,_⟩ | ⟨h1,h2⟩
  · exact h
  · have h1v := congrArg Fin.val h1
    have h2v := congrArg Fin.val h2
    have hi := i.isLt
    have hj := j.isLt
    simp only [next] at h1v h2v
    split_ifs at h1v h2v <;> dsimp at h1v h2v <;> omega

end CyclicInterface

namespace Wheel

private def rimVertex (i : Fin 4) : Wheel.Label := ⟨i.val + 1,by omega⟩

private theorem rimVertex_injective : Function.Injective rimVertex := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change i.val + 1 = j.val + 1 at hv
  omega

private theorem wheel_kappa (i : Fin 4) :
    wheelGraphData.kappa i = s(rimVertex i,rimVertex (CyclicInterface.next (by decide) i)) := by
  fin_cases i <;> rfl

/-- Actual fixed W4 local U*, proved from start/finish via cyclic edges.
The general cyclic uniqueness lemma is consumed on the genuine rim endpoints. -/
theorem wheel_uniqueInterface : wheelGraphData.UniqueInterface (0 : Fin 4) := by
  intro d hd
  rw [wheel_kappa d,wheel_kappa 0] at hd
  have hcyc : s(d,CyclicInterface.next (by decide) d) =
      s((0 : Fin 4),CyclicInterface.next (by decide) 0) := by
    rcases Sym2.eq_iff.mp hd with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · apply Sym2.eq_iff.mpr
      exact Or.inl ⟨rimVertex_injective ha,rimVertex_injective hb⟩
    · apply Sym2.eq_iff.mpr
      exact Or.inr ⟨rimVertex_injective ha,rimVertex_injective hb⟩
  exact CyclicInterface.cyclic_edge_injective (by decide) hcyc

/-- Physical W4 deletion is the existing literal E, using the local corollary. -/
theorem wheel_E_edge : wheelGraphData.E_edge (0 : Fin 4) = E :=
  (wheelGraphData.E_edge_eq_without 0 wheel_uniqueInterface).trans wheelOriginalRoot.2

/-- Actual W4 indexing consumes the corrected raw formula with its existing E.
This remains row algebra; no actual glued graph theorem is assumed or claimed. -/
theorem wheel_physical_row_transport (X : Finset Wheel.Label) (e : Wheel.Label)
    (left : Rows Wheel.Label) (hleft : left.ground = insert e X)
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y) :
    (physicalTransportedRows X Y e left wheelGraphData 0 hleft rfl heX heY).root =
      phi X Y Z (restrict X left.root) (rawLink X e left.root) E := by
  have ht := physical_row_transport X Y e left wheelGraphData 0
    hleft rfl heX heY hXY
  have hr : wheelGraphData.rows.row (0 : Fin 4) = R := fundamental_rows 0
  have hz : Y \ R = Z := by decide
  simpa only [hr,hz,wheel_E_edge] using ht

end Wheel
end D5.S3.Geometry.OriginalLabelTwoSum
