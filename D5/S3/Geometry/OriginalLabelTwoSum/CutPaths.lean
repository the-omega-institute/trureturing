/- GID: D5/S3/Geometry/OriginalLabelTwoSum/CutPaths
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/CutPaths
   mirror-E: none(waiver:original-label-cut-paths)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Constructed oriented path splices, disjoint supports, and exact physical-edge replacement in the actual glued tree. -/
import D5.S3.Geometry.OriginalLabelTwoSum.CutTree

/-! SOURCE ONLY: proof terms have not been elaborated. -/
noncomputable section
open SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.CutTree
universe u v

/-- Choose the unique finite simple path of an original or constructed tree. -/
def treePath {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) (x y : V) : G.Walk x y :=
  Classical.choose (hG.existsUnique_path x y)

theorem treePath_isPath {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) (x y : V) :
    (treePath hG x y).IsPath :=
  (Classical.choose_spec (hG.existsUnique_path x y)).1

theorem treePath_eq {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) : treePath hG x y = p :=
  ((Classical.choose_spec (hG.existsUnique_path x y)).2 p hp).symm

namespace Input
variable {VL : Type u} {VR : Type v} (g : Input VL VR)

abbrev leftPath (x y : VL) := treePath g.leftTree x y
abbrev rightPath (x y : VR) := treePath g.rightTree x y
abbrev path (w z : g.Carrier) := treePath g.isTree w z

/-- The full right path is literally mapped, with original orientation. -/
theorem right_path (x y : VR) :
    g.path (g.qR x) (g.qR y) = (g.rightPath x y).map g.rightHom := by
  have h : ((g.rightPath x y).map g.rightHom).IsPath :=
    (treePath_isPath g.rightTree x y).map g.qR_injective
  exact treePath_eq g.isTree _ h

theorem right_path_edge_mem (x y : VR) (e : Sym2 g.Carrier) :
    e ∈ (g.path (g.qR x) (g.qR y)).edges ↔
      ∃ d ∈ (g.rightPath x y).edges, Sym2.map g.qR d = e := by
  rw [g.right_path]
  simpa only [SimpleGraph.Walk.edges_map,List.mem_map]

/-- An avoiding left walk is mapped through the actual deleted-edge graph. -/
def avoidingImage {x y : VL} (p : g.TL.Walk x y)
    (hp : s(g.aL,g.bL) ∉ p.edges) : g.tree.Walk (g.qL x) (g.qL y) :=
  (p.toDeleteEdge s(g.aL,g.bL) hp).map g.leftHom

theorem avoidingImage_edges {x y : VL} (p : g.TL.Walk x y) (hp) :
    (g.avoidingImage p hp).edges = p.edges.map (Sym2.map g.qL) := by
  simp [avoidingImage,SimpleGraph.Walk.edges_transfer]

theorem avoidingImage_isPath {x y : VL} (p : g.TL.Walk x y) (hp)
    (hpath : p.IsPath) : (g.avoidingImage p hp).IsPath :=
  (hpath.transfer _).map g.qL_injective

theorem left_path_avoiding {x y : VL} (p : g.TL.Walk x y) (hp : p.IsPath)
    (he : s(g.aL,g.bL) ∉ p.edges) :
    g.path (g.qL x) (g.qL y) = g.avoidingImage p he :=
  treePath_eq g.isTree _ (g.avoidingImage_isPath p he hp)

/-- The actual unique right terminal path, copied only to express the two
proved endpoint equalities in the carrier. -/
def terminalPath : g.tree.Walk (g.qL g.aL) (g.qL g.bL) :=
  ((g.rightPath g.aR g.bR).map g.rightHom).copy g.qR_a g.qR_b

theorem terminalPath_isPath : g.terminalPath.IsPath := by
  have h : ((g.rightPath g.aR g.bR).map g.rightHom).IsPath :=
    (treePath_isPath g.rightTree g.aR g.bR).map g.qR_injective
  simpa only [terminalPath,SimpleGraph.Walk.isPath_copy] using h

/-- The forward splice writes the common endpoints once, using Walk.append. -/
def spliceAB {x y : VL} (p₀ : g.cut.Walk x g.aL) (p₁ : g.cut.Walk g.bL y) :
    g.tree.Walk (g.qL x) (g.qL y) :=
  ((p₀.map g.leftHom).append g.terminalPath).append (p₁.map g.leftHom)

/-- The opposite orientation is retained by reversal, not by equating oriented
walks having different endpoint types. -/
def spliceBA {x y : VL} (p₀ : g.cut.Walk x g.bL) (p₁ : g.cut.Walk g.aL y) :
    g.tree.Walk (g.qL x) (g.qL y) :=
  (g.spliceAB p₁.reverse p₀.reverse).reverse

/-- A left cut walk ending at aL cannot contain bL. Consequently its mapped
support meets any right-image vertex only at aL. -/
theorem support_overlap_a {x z : VL} (p : g.cut.Walk x g.aL)
    (hz : z ∈ p.support) {r : VR} (he : g.qL z = g.qR r) : z = g.aL := by
  rcases (g.overlap z r).mp he with ⟨h,_⟩ | ⟨h,_⟩
  · exact h
  · subst z
    exact False.elim (g.cut_separated (CutWalk.support_reachable p hz))

/-- The symmetric endpoint statement uses the same physical cut. -/
theorem support_overlap_b {y z : VL} (p : g.cut.Walk g.bL y)
    (hz : z ∈ p.support) {r : VR} (he : g.qL z = g.qR r) : z = g.bL := by
  classical
  rcases (g.overlap z r).mp he with ⟨h,_⟩ | ⟨h,_⟩
  · subst z
    have h := (p.takeUntil g.aL hz).reachable
    exact False.elim (g.cut_separated h.symm)
  · exact h

/-- The two finite left segments have disjoint supports, as they belong to
opposite cut components. This is proved from original-tree acyclicity. -/
theorem segments_disjoint {x y z : VL} (p₀ : g.cut.Walk x g.aL)
    (p₁ : g.cut.Walk g.bL y) (h₀ : z ∈ p₀.support) (h₁ : z ∈ p₁.support) : False := by
  classical
  have ha := CutWalk.support_reachable p₀ h₀
  have hb := (p₁.takeUntil z h₁).reachable
  exact g.cut_separated (ha.trans hb.symm)

/-- Pathness of the constructed splice is proved by support separation at
both attachment vertices. No connectedness/path equation is an input. -/
theorem spliceAB_isPath {x y : VL} (p₀ : g.cut.Walk x g.aL)
    (p₁ : g.cut.Walk g.bL y) (h₀ : p₀.IsPath) (h₁ : p₁.IsPath) :
    (g.spliceAB p₀ p₁).IsPath := by
  classical
  have hm₀ : (p₀.map g.leftHom).IsPath := h₀.map g.qL_injective
  have hm₁ : (p₁.map g.leftHom).IsPath := h₁.map g.qL_injective
  have hi₀ : ∀ z, z ∈ (p₀.map g.leftHom).support →
      z ∈ g.terminalPath.support → z = g.qL g.aL := by
    intro z hz ht
    simp only [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨l,hl,rfl⟩ := hz
    simp only [terminalPath,SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map,List.mem_map] at ht
    obtain ⟨r,hr,he⟩ := ht
    exact congrArg g.qL (g.support_overlap_a p₀ hl he.symm)
  have hfirst := CutWalk.append_path hm₀ g.terminalPath_isPath hi₀
  apply CutWalk.append_path hfirst hm₁
  intro z hz hz₁
  simp only [SimpleGraph.Walk.support_map,List.mem_map] at hz₁
  obtain ⟨l,hl,rfl⟩ := hz₁
  rcases SimpleGraph.Walk.mem_support_append_iff.mp hz with hz₀ | ht
  · simp only [SimpleGraph.Walk.support_map,List.mem_map] at hz₀
    obtain ⟨k,hk,he⟩ := hz₀
    have hkl : k = l := g.qL_injective he
    exact False.elim (g.segments_disjoint p₀ p₁ (hkl ▸ hk) hl)
  · simp only [terminalPath,SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map,List.mem_map] at ht
    obtain ⟨r,hr,he⟩ := ht
    exact congrArg g.qL (g.support_overlap_b p₁ hl he.symm)

theorem spliceBA_isPath {x y : VL} (p₀ : g.cut.Walk x g.bL)
    (p₁ : g.cut.Walk g.aL y) (h₀ : p₀.IsPath) (h₁ : p₁.IsPath) :
    (g.spliceBA p₀ p₁).IsPath :=
  (g.spliceAB_isPath p₁.reverse p₀.reverse h₁.reverse h₀.reverse).reverse

/-- Exact physical-edge membership in the constructed forward splice. -/
theorem spliceAB_edge_mem {x y : VL} (p₀ : g.cut.Walk x g.aL)
    (p₁ : g.cut.Walk g.bL y) (e : Sym2 g.Carrier) :
    e ∈ (g.spliceAB p₀ p₁).edges ↔
      (∃ d, (d ∈ p₀.edges ∨ d ∈ p₁.edges) ∧ Sym2.map g.qL d = e) ∨
      ∃ d ∈ (g.rightPath g.aR g.bR).edges, Sym2.map g.qR d = e := by
  simp only [spliceAB,terminalPath,SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_copy,SimpleGraph.Walk.edges_map,List.mem_append,List.mem_map]
  change ((∃ d ∈ p₀.edges, Sym2.map g.qL d = e) ∨
      (∃ d ∈ (g.rightPath g.aR g.bR).edges, Sym2.map g.qR d = e)) ∨
      (∃ d ∈ p₁.edges, Sym2.map g.qL d = e) ↔ _
  aesop

theorem spliceBA_edge_mem {x y : VL} (p₀ : g.cut.Walk x g.bL)
    (p₁ : g.cut.Walk g.aL y) (e : Sym2 g.Carrier) :
    e ∈ (g.spliceBA p₀ p₁).edges ↔
      (∃ d, (d ∈ p₀.edges ∨ d ∈ p₁.edges) ∧ Sym2.map g.qL d = e) ∨
      ∃ d ∈ (g.rightPath g.aR g.bR).edges, Sym2.map g.qR d = e := by
  simp only [spliceBA,SimpleGraph.Walk.edges_reverse,List.mem_reverse]
  rw [g.spliceAB_edge_mem]
  simp only [SimpleGraph.Walk.edges_reverse,List.mem_reverse]
  aesop

/-- In either orientation of an actual occurrence, split exactly there and
splice in the right terminal path. The displayed equations are well typed. -/
theorem left_path_using {x y : VL} (p : g.TL.Walk x y) (hp : p.IsPath)
    (he : s(g.aL,g.bL) ∈ p.edges) :
    (∃ (h : g.TL.Adj g.aL g.bL) (p₀ : g.TL.Walk x g.aL)
        (p₁ : g.TL.Walk g.bL y) (h₀ : s(g.aL,g.bL) ∉ p₀.edges)
        (h₁ : s(g.aL,g.bL) ∉ p₁.edges),
      p = p₀.append (.cons h p₁) ∧
      g.path (g.qL x) (g.qL y) =
        g.spliceAB (p₀.toDeleteEdge _ h₀) (p₁.toDeleteEdge _ h₁)) ∨
    (∃ (h : g.TL.Adj g.bL g.aL) (p₀ : g.TL.Walk x g.bL)
        (p₁ : g.TL.Walk g.aL y) (h₀ : s(g.aL,g.bL) ∉ p₀.edges)
        (h₁ : s(g.aL,g.bL) ∉ p₁.edges),
      p = p₀.append (.cons h p₁) ∧
      g.path (g.qL x) (g.qL y) =
        g.spliceBA (p₀.toDeleteEdge _ h₀) (p₁.toDeleteEdge _ h₁)) := by
  classical
  rcases CutWalk.split_edge p he with ⟨h,p₀,p₁,hs⟩ | ⟨h,p₀,p₁,hs⟩
  · have hpath : (p₀.append (.cons h p₁)).IsPath := hs ▸ hp
    obtain ⟨h₀,h₁⟩ := CutWalk.split_avoids h p₀ p₁ hpath
    refine Or.inl ⟨h,p₀,p₁,h₀,h₁,hs,?_⟩
    exact treePath_eq g.isTree _ (g.spliceAB_isPath _ _
      (hpath.of_append_left.transfer _)
      (hpath.of_append_right.of_cons.transfer _))
  · have hpath : (p₀.append (.cons h p₁)).IsPath := hs ▸ hp
    have hn := CutWalk.split_avoids h p₀ p₁ hpath
    have h₀ : s(g.aL,g.bL) ∉ p₀.edges := by simpa [Sym2.eq_swap] using hn.1
    have h₁ : s(g.aL,g.bL) ∉ p₁.edges := by simpa [Sym2.eq_swap] using hn.2
    refine Or.inr ⟨h,p₀,p₁,h₀,h₁,hs,?_⟩
    exact treePath_eq g.isTree _ (g.spliceBA_isPath _ _
      (hpath.of_append_left.transfer _)
      (hpath.of_append_right.of_cons.transfer _))

/-- Exact substitution of PHYSICAL edges. No chord-index injectivity is used.
The right path contributes iff the deleted left edge occurs. -/
theorem left_path_edge_mem {x y : VL} (p : g.TL.Walk x y) (hp : p.IsPath)
    (e : Sym2 g.Carrier) :
    e ∈ (g.path (g.qL x) (g.qL y)).edges ↔
      (∃ d ∈ p.edges, d ≠ s(g.aL,g.bL) ∧ Sym2.map g.qL d = e) ∨
      (s(g.aL,g.bL) ∈ p.edges ∧
        ∃ d ∈ (g.rightPath g.aR g.bR).edges, Sym2.map g.qR d = e) := by
  classical
  by_cases he : s(g.aL,g.bL) ∈ p.edges
  · rcases g.left_path_using p hp he with
      ⟨h,p₀,p₁,h₀,h₁,hs,hw⟩ | ⟨h,p₀,p₁,h₀,h₁,hs,hw⟩
    · rw [hw,g.spliceAB_edge_mem]
      simp only [SimpleGraph.Walk.edges_transfer]
      rw [hs]
      simp only [SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_cons,
        List.mem_append,List.mem_cons]
      -- Only propositional set membership remains; pathness was proved above.
      aesop
    · rw [hw,g.spliceBA_edge_mem]
      simp only [SimpleGraph.Walk.edges_transfer]
      rw [hs]
      simp only [SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_cons,
        List.mem_append,List.mem_cons]
      have hswap : s(g.bL,g.aL) = s(g.aL,g.bL) := Sym2.eq_swap
      rw [hswap]
      aesop
  · rw [g.left_path_avoiding p hp he,g.avoidingImage_edges]
    simp only [List.mem_map,he,false_and,or_false]
    constructor
    · rintro ⟨d,hd,hde⟩
      exact ⟨d,hd,fun hd' => he (hd' ▸ hd),hde⟩
    · rintro ⟨d,hd,_,hde⟩
      exact ⟨d,hd,hde⟩

/-- The requested set equation, including both orientations and all untouched
left paths, as a consequence of the constructed path theorem. -/
theorem left_path_edgeSet (x y : VL) :
    (g.path (g.qL x) (g.qL y)).edgeSet =
      Sym2.map g.qL '' ((g.leftPath x y).edgeSet \ {s(g.aL,g.bL)}) ∪
      (if s(g.aL,g.bL) ∈ (g.leftPath x y).edges then
        Sym2.map g.qR '' (g.rightPath g.aR g.bR).edgeSet else ∅) := by
  classical
  ext e
  rw [SimpleGraph.Walk.mem_edgeSet,g.left_path_edge_mem _ (treePath_isPath _ _ _)]
  by_cases h : s(g.aL,g.bL) ∈ (g.leftPath x y).edges <;>
    simp [h,Set.mem_image,SimpleGraph.Walk.mem_edgeSet,and_assoc]

theorem right_path_edgeSet (x y : VR) :
    (g.path (g.qR x) (g.qR y)).edgeSet =
      Sym2.map g.qR '' (g.rightPath x y).edgeSet := by
  ext e
  exact g.right_path_edge_mem x y e
end Input
end D5.S3.Geometry.OriginalLabelTwoSum.CutTree
