/- GID: D5/S3/Geometry/OriginalLabelTwoSum/CutTree
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/CutTree
   mirror-E: none(waiver:original-label-cut-tree)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: The literal cut-left/full-right edge-image union is a tree on the explicit infinite-capable carrier. -/
import D5.S3.Geometry.OriginalLabelTwoSum.CutWalk

/-! SOURCE ONLY. Input contains only the two original trees and their terminal
facts; it contains no assertion about the constructed graph or its paths. -/
noncomputable section
open SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.CutTree
universe u v

structure Input (VL : Type u) (VR : Type v) where
  TL : SimpleGraph VL
  TR : SimpleGraph VR
  aL : VL
  bL : VL
  aR : VR
  bR : VR
  neL : aL ≠ bL
  neR : aR ≠ bR
  leftTree : TL.IsTree
  rightTree : TR.IsTree
  edge : TL.Adj aL bL

namespace Input
variable {VL : Type u} {VR : Type v} (g : Input VL VR)

abbrev Carrier := VL ⊕ {z : VR // z ≠ g.aR ∧ z ≠ g.bR}
abbrev cut := g.TL.deleteEdges {s(g.aL,g.bL)}
def qL (x : VL) : g.Carrier := Sum.inl x
def qR (y : VR) : g.Carrier := by
  classical
  exact if ha : y = g.aR then g.qL g.aL else
    if hb : y = g.bR then g.qL g.bL else Sum.inr ⟨y,ha,hb⟩

@[simp] theorem qR_a : g.qR g.aR = g.qL g.aL := by simp [qR]
@[simp] theorem qR_b : g.qR g.bR = g.qL g.bL := by
  simp [qR, Ne.symm g.neR]

theorem qL_injective : Function.Injective g.qL := Sum.inl_injective

theorem qR_injective : Function.Injective g.qR := by
  classical
  intro x y h
  by_cases hxa : x = g.aR
  · subst x
    by_cases hya : y = g.aR
    · exact hya.symm
    by_cases hyb : y = g.bR
    · subst y
      have : g.aL = g.bL := g.qL_injective (by simpa using h)
      exact False.elim (g.neL this)
    · simp [qR,hya,hyb,qL,Ne.symm g.neR] at h
  by_cases hxb : x = g.bR
  · subst x
    by_cases hya : y = g.aR
    · subst y
      have : g.bL = g.aL := g.qL_injective (by simpa using h)
      exact False.elim (g.neL this.symm)
    by_cases hyb : y = g.bR
    · exact hyb.symm
    · simp [qR,hya,hyb,qL,Ne.symm g.neR] at h
  by_cases hya : y = g.aR
  · simp [qR,hxa,hxb,hya,qL] at h
  by_cases hyb : y = g.bR
  · simp [qR,hxa,hxb,hyb,qL,Ne.symm g.neR] at h
  · simpa [qR,hxa,hxb,hya,hyb] using h

/-- Exact overlap, with both terminal identifications and no others. -/
theorem overlap (x : VL) (y : VR) :
    g.qL x = g.qR y ↔
      (x = g.aL ∧ y = g.aR) ∨ (x = g.bL ∧ y = g.bR) := by
  classical
  by_cases ha : y = g.aR
  · subst y
    simp [qL,g.neR]
  by_cases hb : y = g.bR
  · subst y
    simp [qL,Ne.symm g.neR]
  · simp [qR,ha,hb,qL]

theorem cover (w : g.Carrier) : (∃ x, g.qL x = w) ∨ (∃ y, g.qR y = w) := by
  classical
  cases w with
  | inl x => exact Or.inl ⟨x,rfl⟩
  | inr y => exact Or.inr ⟨y.1,by simp [qR,y.2.1,y.2.2]⟩

theorem range_intersection : Set.range g.qL ∩ Set.range g.qR =
    {g.qL g.aL, g.qL g.bL} := by
  ext w
  constructor
  · rintro ⟨⟨x,rfl⟩,⟨y,hy⟩⟩
    rcases (g.overlap x y).mp hy.symm with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp
  · intro hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact ⟨⟨_,rfl⟩,⟨g.aR,g.qR_a⟩⟩
    · exact ⟨⟨_,rfl⟩,⟨g.bR,g.qR_b⟩⟩

def leftEmbedding : VL ↪ g.Carrier := ⟨g.qL,g.qL_injective⟩
def rightEmbedding : VR ↪ g.Carrier := ⟨g.qR,g.qR_injective⟩

/-- Delete the left edge, map all remaining left edges, and map the ENTIRE
right tree. No right tree edge is removed. -/
def tree : SimpleGraph g.Carrier :=
  g.cut.map g.leftEmbedding ⊔ g.TR.map g.rightEmbedding

theorem adjacency (w z : g.Carrier) : g.tree.Adj w z ↔
    (∃ x y, g.cut.Adj x y ∧ g.qL x = w ∧ g.qL y = z) ∨
    (∃ x y, g.TR.Adj x y ∧ g.qR x = w ∧ g.qR y = z) := by
  simp only [tree,SimpleGraph.sup_adj,SimpleGraph.map_adj]
  rfl

theorem edgeSet : g.tree.edgeSet =
    Sym2.map g.qL '' g.cut.edgeSet ∪ Sym2.map g.qR '' g.TR.edgeSet := by
  simp only [tree,SimpleGraph.edgeSet_sup,SimpleGraph.edgeSet_map]
  all_goals rfl

theorem no_loops (w : g.Carrier) : ¬g.tree.Adj w w := g.tree.loopless.irrefl w

def leftHom : g.cut →g g.tree where
  toFun := g.qL
  map_rel' := fun h => (g.adjacency _ _).mpr (Or.inl ⟨_,_,h,rfl,rfl⟩)

def rightHom : g.TR →g g.tree where
  toFun := g.qR
  map_rel' := fun h => (g.adjacency _ _).mpr (Or.inr ⟨_,_,h,rfl,rfl⟩)

/-- Extend compatible predicates on the two original vertex types. -/
def predicate (P : VL → Prop) (Q : VR → Prop) : g.Carrier → Prop :=
  Sum.elim P (fun z => Q z.1)

@[simp] theorem predicate_qL (P : VL → Prop) (Q : VR → Prop) (x : VL) :
    g.predicate P Q (g.qL x) ↔ P x := Iff.rfl

theorem predicate_qR (P : VL → Prop) (Q : VR → Prop)
    (ha : P g.aL ↔ Q g.aR) (hb : P g.bL ↔ Q g.bR) (y : VR) :
    g.predicate P Q (g.qR y) ↔ Q y := by
  classical
  by_cases hya : y = g.aR
  · subst y; simpa using ha
  by_cases hyb : y = g.bR
  · subst y; simpa using hb
  · simp [qR,hya,hyb,predicate]

theorem cut_separated : ¬g.cut.Reachable g.aL g.bL :=
  CutWalk.separated g.leftTree g.edge

theorem cut_cover (x : VL) : g.cut.Reachable g.aL x ∨ g.cut.Reachable g.bL x :=
  CutWalk.cover g.leftTree.connected g.aL g.bL x

theorem cut_side_adj {x y : VL} (h : g.cut.Adj x y) :
    g.cut.Reachable g.aL x ↔ g.cut.Reachable g.aL y :=
  CutWalk.side_iff h.reachable

/-- Every vertex connects to a terminal of its original summand by a finite
walk. The two left components connect through the original right terminal walk. -/
theorem connected : g.tree.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable g.tree).mpr
  refine ⟨g.qL g.aL,?_⟩
  intro w
  have hab : g.tree.Reachable (g.qL g.aL) (g.qL g.bL) := by
    simpa only [rightHom,SimpleGraph.Hom.coe_mk,g.qR_a,g.qR_b] using
      (g.rightTree.connected g.aR g.bR).map g.rightHom
  rcases g.cover w with ⟨x,rfl⟩ | ⟨y,rfl⟩
  · rcases g.cut_cover x with hx | hx
    · exact hx.map g.leftHom
    · exact hab.trans (hx.map g.leftHom)
  · simpa only [rightHom,SimpleGraph.Hom.coe_mk,g.qR_a] using
      (g.rightTree.connected g.aR y).map g.rightHom

/-- Each retained left edge is still a bridge. Its original cut predicate is
constant on BOTH left terminals, so it extends constantly over the right tree. -/
theorem left_bridge {x y : VL} (hxy : g.cut.Adj x y) :
    g.tree.IsBridge s(g.qL x,g.qL y) := by
  classical
  let D := g.TL.deleteEdges {s(x,y)}
  let P : VL → Prop := D.Reachable x
  let Q : VR → Prop := fun _ => P g.aL
  have hne : s(g.aL,g.bL) ≠ s(x,y) := by
    have := (SimpleGraph.deleteEdges_adj.mp hxy).2
    simpa [eq_comm] using this
  have hab : D.Adj g.aL g.bL :=
    SimpleGraph.deleteEdges_adj.mpr ⟨g.edge,by simpa using hne⟩
  have hb : P g.bL ↔ P g.aL := (CutWalk.side_iff hab.reachable).symm
  have hR (z : VR) : g.predicate P Q (g.qR z) ↔ P g.aL :=
    g.predicate_qR P Q Iff.rfl hb z
  apply CutWalk.bridge_of_predicate (g.predicate P Q)
  · exact SimpleGraph.Reachable.rfl
  · exact CutWalk.separated g.leftTree ((SimpleGraph.deleteEdges_le _) hxy)
  · intro w z hwz hnot
    rcases (g.adjacency w z).mp hwz with ⟨u,v,hu,rfl,rfl⟩ | ⟨u,v,hu,rfl,rfl⟩
    · have hsource : s(u,v) ≠ s(x,y) := by
        intro he
        apply hnot
        exact congrArg (Sym2.map g.qL) he
      have hd : D.Adj u v := SimpleGraph.deleteEdges_adj.mpr
        ⟨(SimpleGraph.deleteEdges_le _) hu,by simpa using hsource⟩
      rw [g.predicate_qL,g.predicate_qL]
      exact CutWalk.side_iff hd.reachable
    · exact (hR u).trans (hR v).symm

/-- Each full-right edge is a bridge. Extend its two cut classes over the left
forest by the already PROVED aL/bL component partition. -/
theorem right_bridge {x y : VR} (hxy : g.TR.Adj x y) :
    g.tree.IsBridge s(g.qR x,g.qR y) := by
  classical
  let D := g.TR.deleteEdges {s(x,y)}
  let Q : VR → Prop := D.Reachable x
  let P : VL → Prop := fun z =>
    if g.cut.Reachable g.aL z then Q g.aR else Q g.bR
  have ha : P g.aL ↔ Q g.aR := by simp [P]
  have hb : P g.bL ↔ Q g.bR := by simp [P,g.cut_separated]
  have hR (z : VR) : g.predicate P Q (g.qR z) ↔ Q z :=
    g.predicate_qR P Q ha hb z
  apply CutWalk.bridge_of_predicate (g.predicate P Q)
  · exact (hR x).mpr .rfl
  · intro hy
    exact CutWalk.separated g.rightTree hxy ((hR y).mp hy)
  · intro w z hwz hnot
    rcases (g.adjacency w z).mp hwz with ⟨u,v,hu,rfl,rfl⟩ | ⟨u,v,hu,rfl,rfl⟩
    · change P u ↔ P v
      have hc := g.cut_side_adj hu
      simp only [P]
      rcases em (g.cut.Reachable g.aL u) with h | h
      · rw [if_pos h,if_pos (hc.mp h)]
      · rw [if_neg h,if_neg (fun hv => h (hc.mpr hv))]
    · have hsource : s(u,v) ≠ s(x,y) := by
        intro he
        exact hnot (congrArg (Sym2.map g.qR) he)
      have hd : D.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨hu,by simpa using hsource⟩
      exact (hR u).trans ((CutWalk.side_iff hd.reachable).trans (hR v).symm)

/-- The actual edge-image graph is a tree, derived from original IsTree
hypotheses and the declared tree edge. No finiteness hypothesis is used. -/
theorem isTree : g.tree.IsTree where
  connected := g.connected
  isAcyclic := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr (by
    intro w z hwz
    rcases (g.adjacency w z).mp hwz with ⟨u,v,hu,rfl,rfl⟩ | ⟨u,v,hu,rfl,rfl⟩
    · exact g.left_bridge hu
    · exact g.right_bridge hu)

/-- Exact adjacency on left images: the right tree can contribute a
terminal-terminal edge, which is recorded explicitly rather than suppressed. -/
theorem adjacency_left (x y : VL) :
    g.tree.Adj (g.qL x) (g.qL y) ↔ g.cut.Adj x y ∨
      (g.TR.Adj g.aR g.bR ∧
        ((x = g.aL ∧ y = g.bL) ∨ (x = g.bL ∧ y = g.aL))) := by
  rw [g.adjacency]
  constructor
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · exact Or.inl (g.qL_injective hu ▸ g.qL_injective hv ▸ h)
    · have hx := (g.overlap x u).mp hu.symm
      have hy := (g.overlap y v).mp hv.symm
      rcases hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        rcases hy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact False.elim (g.TR.loopless.irrefl _ h)
      · exact Or.inr ⟨h,Or.inl ⟨rfl,rfl⟩⟩
      · exact Or.inr ⟨h.symm,Or.inr ⟨rfl,rfl⟩⟩
      · exact False.elim (g.TR.loopless.irrefl _ h)
  · rintro (h | ⟨h,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
    · exact Or.inl ⟨_,_,h,rfl,rfl⟩
    · exact Or.inr ⟨_,_,h,g.qR_a,g.qR_b⟩
    · exact Or.inr ⟨_,_,h.symm,g.qR_b,g.qR_a⟩

/-- The entire mapped right tree is induced. A left cut edge cannot connect
the two terminal images, because that is precisely the edge deleted. -/
theorem adjacency_right (x y : VR) :
    g.tree.Adj (g.qR x) (g.qR y) ↔ g.TR.Adj x y := by
  rw [g.adjacency]
  constructor
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · have hx := (g.overlap u x).mp hu
      have hy := (g.overlap v y).mp hv
      have hc := SimpleGraph.deleteEdges_adj.mp h
      rcases hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        rcases hy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact False.elim (g.TL.loopless.irrefl _ hc.1)
      · exact False.elim (hc.2 (by simp))
      · exact False.elim (hc.2 (by simp [Sym2.eq_swap]))
      · exact False.elim (g.TL.loopless.irrefl _ hc.1)
    · exact g.qR_injective hu ▸ g.qR_injective hv ▸ h
  · intro h
    exact Or.inr ⟨_,_,h,rfl,rfl⟩
/-- No physical edge of the retained left forest coincides with a physical
edge of the entire right tree. The only possible cross-image nonloop pair is
the terminal pair, and that pair was removed on the left. -/
theorem cross_edge_ne {x y : VL} {r s : VR} (hxy : g.cut.Adj x y)
    (_hrs : g.TR.Adj r s) :
    Sym2.map g.qL s(x,y) ≠ Sym2.map g.qR s(r,s) := by
  have impossible : ∀ r s, g.qL x = g.qR r → g.qL y = g.qR s → False := by
    intro r s hx hy
    have hx' := (g.overlap x r).mp hx
    have hy' := (g.overlap y s).mp hy
    have hc := SimpleGraph.deleteEdges_adj.mp hxy
    rcases hx' with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;>
      rcases hy' with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact g.TL.loopless.irrefl _ hc.1
    · exact hc.2 (by simp)
    · exact hc.2 (by simp [Sym2.eq_swap])
    · exact g.TL.loopless.irrefl _ hc.1
  intro he
  simp only [Sym2.map_mk,Sym2.eq_iff] at he
  rcases he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact impossible r s hx hy
  · exact impossible s r hx hy

theorem edge_images_disjoint :
    Disjoint (Sym2.map g.qL '' g.cut.edgeSet)
      (Sym2.map g.qR '' g.TR.edgeSet) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨d,hd,rfl⟩ ⟨f,hf,he⟩
  induction d using Sym2.ind with
  | h x y =>
    induction f using Sym2.ind with
    | h r s => exact g.cross_edge_ne hd hf he.symm
end Input
end D5.S3.Geometry.OriginalLabelTwoSum.CutTree
