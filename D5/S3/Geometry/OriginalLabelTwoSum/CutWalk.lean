/- GID: D5/S3/Geometry/OriginalLabelTwoSum/CutWalk
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/CutWalk
   mirror-E: none(waiver:original-label-cut-walk)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Finite-walk cut invariants and an actual two-component edge deletion for arbitrary trees. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! SOURCE ONLY: no elaboration or kernel receipt has been produced. -/
noncomputable section
open SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.CutWalk
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A predicate constant across edges is constant along every finite walk. -/
theorem invariant {P : V → Prop} (h : ∀ x y, G.Adj x y → (P x ↔ P y))
    {x y : V} (p : G.Walk x y) : P x ↔ P y := by
  induction p with
  | nil => rfl
  | @cons x z y hx p ih => exact (h x z hx).trans ih

theorem side_iff {x y z : V} (h : G.Reachable x y) :
    G.Reachable z x ↔ G.Reachable z y :=
  ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩

/-- To prove an edge is a bridge it suffices to separate its endpoints by an
invariant of the graph with precisely that physical edge removed. -/
theorem bridge_of_predicate {a b : V} (P : V → Prop) (ha : P a) (hb : ¬P b)
    (h : ∀ x y, G.Adj x y → s(x,y) ≠ s(a,b) → (P x ↔ P y)) :
    G.IsBridge s(a,b) := by
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  have hi := invariant (G := G.deleteEdges {s(a,b)}) (P := P) (by
    intro x y hxy
    obtain ⟨hadj,hne⟩ := SimpleGraph.deleteEdges_adj.mp hxy
    exact h x y hadj (by simpa using hne)) p
  exact hb (hi.mp ha)

/-- A tree edge really disconnects its two endpoints, including on infinite
vertex types. This is mathlib's bridge characterization, with no edge counts. -/
theorem separated (hG : G.IsTree) {a b : V} (hab : G.Adj a b) :
    ¬(G.deleteEdges {s(a,b)}).Reachable a b :=
  SimpleGraph.isBridge_iff.mp
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hab)

/-- Removing an edge from a connected graph leaves no components other than
the two endpoint components (these may coincide for a nonbridge). -/
theorem cover (hG : G.Connected) (a b x : V) :
    (G.deleteEdges {s(a,b)}).Reachable a x ∨
      (G.deleteEdges {s(a,b)}).Reachable b x := by
  let F := G.deleteEdges {s(a,b)}
  have propagate : ∀ {u v : V}, G.Walk u v →
      (F.Reachable a u ∨ F.Reachable b u) →
        (F.Reachable a v ∨ F.Reachable b v) := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u z v huz p ih =>
      intro hu
      apply ih
      by_cases he : s(u,z) = s(a,b)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr .rfl
        · exact Or.inl .rfl
      · have hz : F.Adj u z := SimpleGraph.deleteEdges_adj.mpr ⟨huz,by simpa using he⟩
        exact hu.elim (fun h => Or.inl (h.trans hz.reachable))
          (fun h => Or.inr (h.trans hz.reachable))
  exact (hG a x).elim fun p => propagate p (Or.inl .rfl)

theorem support_reachable {x y z : V} (p : G.Walk x y) (hz : z ∈ p.support) :
    G.Reachable y z := by
  classical
  exact p.reachable.symm.trans (p.takeUntil z hz).reachable

/-- Concatenation at one common support vertex is a path. The support proof
uses nodup, and is independent of ambient vertex cardinality. -/
theorem append_path {x y z : V} {p : G.Walk x y} {q : G.Walk y z}
    (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ t, t ∈ p.support → t ∈ q.support → t = y) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  apply List.disjoint_left.mpr
  intro t ht htq
  have he := hi t ht (List.mem_of_mem_tail htq)
  subst t
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 htq

/-- Split at an actual occurrence of an unordered edge, retaining orientation.
This is proved by recursion on Walk; no path-splice API is postulated. -/
theorem split_edge {a b x y : V} (p : G.Walk x y) (he : s(a,b) ∈ p.edges) :
    (∃ (h : G.Adj a b) (p₀ : G.Walk x a) (p₁ : G.Walk b y),
      p = p₀.append (.cons h p₁)) ∨
    (∃ (h : G.Adj b a) (p₀ : G.Walk x b) (p₁ : G.Walk a y),
      p = p₀.append (.cons h p₁)) := by
  induction p with
  | nil => simp at he
  | @cons x z y hx p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨hx,.nil,p,rfl⟩
      · exact Or.inr ⟨hx,.nil,p,rfl⟩
    · rcases ih he with ⟨h,p₀,p₁,hp⟩ | ⟨h,p₀,p₁,hp⟩
      · exact Or.inl ⟨h,.cons hx p₀,p₁,by rw [hp]; rfl⟩
      · exact Or.inr ⟨h,.cons hx p₀,p₁,by rw [hp]; rfl⟩

/-- In a simple path, neither side of the selected edge contains another
occurrence of that physical edge. -/
theorem split_avoids {a b x y : V} (h : G.Adj a b)
    (p₀ : G.Walk x a) (p₁ : G.Walk b y)
    (hp : (p₀.append (.cons h p₁)).IsPath) :
    s(a,b) ∉ p₀.edges ∧ s(a,b) ∉ p₁.edges := by
  have hn := hp.edges_nodup
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
    List.nodup_append'] at hn
  constructor
  · intro he
    exact hn.2.2 he (by simp)
  · exact (List.nodup_cons.mp hn.2.1).1
end D5.S3.Geometry.OriginalLabelTwoSum.CutWalk
