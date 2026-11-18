/- GID: D5/S3/Combinatorics/Graph/Incidence/TreeParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/TreeParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even indegrees and prescribed odd-degree vertices in finite trees. -/

import D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.TreeParity

open SimpleGraph
open scoped Sym2 BigOperators

section

variable {V : Type} {G : SimpleGraph V}

open Finset
open D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge
  (deletedSide deletedSide_connected deletedSide_cover deletedSide_disjoint)

private abbrev cutSide (G : SimpleGraph V) (u v : V) : Set V := deletedSide G u v v

/-- The number of edges whose chosen head is `v`. -/
noncomputable def indegree (head : G.edgeSet → V) (v : V) : ℕ :=
  Nat.card {e : G.edgeSet // head e = v}

private theorem cut_side_indegree_sum [Fintype V] (hT : G.IsTree)
    (head : G.edgeSet → V) (hhead : ∀ e, head e ∈ e.val) {u v : V} (huv : G.Adj u v) :
    letI := Classical.propDecidable
    (∑ x ∈ (cutSide G u v).toFinset, indegree head x) +
        (if head ⟨s(u, v), huv⟩ = v then 0 else 1) = Nat.card (cutSide G u v) := by
  classical
  let D := G.deleteEdges {s(u, v)}
  let S := cutSide G u v
  let cut : G.edgeSet := ⟨s(u, v), huv⟩
  let internal := D.edgeFinset ∩ S.toFinset.sym2
  let into := ((univ : Finset G.edgeSet).filter (fun e => head e ∈ S.toFinset)).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hv : v ∈ S := Reachable.rfl
  have hu : u ∉ S := by
    intro h
    exact (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic huv) h.symm
  have hnot : s(u, v) ∉ internal := by simp [internal, D]
  have hmem (x y : V) (hadj : D.Adj x y) : x ∈ S ↔ y ∈ S :=
    ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  have hcount : into = if head cut = v then insert s(u, v) internal else internal := by
    ext e
    obtain ⟨x, y⟩ := e
    change s(x, y) ∈ into ↔ s(x, y) ∈ _
    by_cases he : s(x, y) = s(u, v)
    · rw [he]
      have hcut : head cut ∈ S ↔ head cut = v := by
        rcases Sym2.mem_iff.mp (hhead cut) with h | h
        · simp [h, hu, huv.ne]
        · simp [h, hv]
      have hinto : s(u, v) ∈ into ↔ head cut ∈ S := by
        simp only [into, mem_map, mem_filter, mem_univ, true_and, Set.mem_toFinset]
        exact ⟨fun ⟨e, h, he⟩ => (show e = cut from Subtype.ext he) ▸ h,
          fun h => ⟨cut, h, rfl⟩⟩
      rw [hinto, hcut]
      split <;> simp_all
    · have hadj : D.Adj x y ↔ G.Adj x y := by simp [D, he]
      rw [show (s(x, y) ∈ (if head cut = v then insert s(u, v) internal else internal)) ↔
          s(x, y) ∈ internal by split <;> simp [he]]
      simp only [into, mem_map, mem_filter, mem_univ, true_and, Set.mem_toFinset,
        internal, mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff]
      constructor
      · rintro ⟨e, h, he'⟩
        change e.val = s(x, y) at he'
        have heG : s(x, y) ∈ G.edgeSet := he' ▸ e.property
        have hd : D.Adj x y := hadj.mpr heG
        refine ⟨hd, ?_⟩
        have hend : head e ∈ s(x, y) := he' ▸ hhead e
        rcases Sym2.mem_iff.mp hend with h' | h'
        · rw [h'] at h
          exact ⟨h, (hmem x y hd).mp h⟩
        · rw [h'] at h
          exact ⟨(hmem x y hd).mpr h, h⟩
      · rintro ⟨hd, hx, hy⟩
        let e : G.edgeSet := ⟨s(x, y), hadj.mp hd⟩
        refine ⟨e, ?_, rfl⟩
        rcases Sym2.mem_iff.mp (hhead e) with h | h
        · simpa [h] using hx
        · simpa [h] using hy
  have hTree : (D.induce S).IsTree :=
    ⟨deletedSide_connected G u v v,
      (hT.isAcyclic.anti (deleteEdges_le _)).induce S⟩
  have hInternal : internal.card + 1 = Nat.card S := by
    change (D.edgeFinset ∩ S.toFinset.sym2).card + 1 = Nat.card ↥S
    rw [← map_edgeFinset_induce, Finset.card_map, Nat.card_eq_fintype_card]
    exact hTree.card_edgeFinset
  have hfib (x : V) : indegree head x = ((univ : Finset G.edgeSet).filter
      (fun e => head e = x)).card := by
    rw [indegree, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum : (∑ x ∈ S.toFinset, indegree head x) = into.card := by
    simp_rw [hfib]
    dsimp [into]
    rw [Finset.card_map]
    exact sum_card_fiberwise_eq_card_filter univ S.toFinset head
  change (∑ x ∈ S.toFinset, indegree head x) + (if head cut = v then 0 else 1) = Nat.card S
  rw [hsum, hcount]
  split
  · rw [card_insert_of_notMem hnot, add_zero]
    exact hInternal
  · exact hInternal

/-- Every even-indegree orientation points into the even side of a cut edge. -/
private theorem head_eq_iff_even_cutSide [Fintype V] (hT : G.IsTree)
    (head : G.edgeSet → V) (hhead : ∀ e, head e ∈ e.val)
    (heven : ∀ x, Even (indegree head x)) {u v : V} (huv : G.Adj u v) :
    head ⟨s(u, v), huv⟩ = v ↔ Even (Nat.card (cutSide G u v)) := by
  classical
  have hsum := cut_side_indegree_sum hT head hhead huv
  have hEvenSum : Even (∑ x ∈ (cutSide G u v).toFinset, indegree head x) :=
    Finset.even_sum _ (fun x _ => heven x)
  rw [← hsum, Nat.even_add, iff_true_left hEvenSum]
  split <;> simp_all

/-- Vertex deletion, retaining the induced graph on all other vertices. -/
abbrev withoutVertex (G : SimpleGraph V) (b : V) := G.induce {x : V | x ≠ b}

/-- The component of `G - b` containing the neighbor `w`. -/
def neighborBranch (G : SimpleGraph V) (b : V) (w : G.neighborSet b) :
    (withoutVertex G b).ConnectedComponent :=
  (withoutVertex G b).connectedComponentMk ⟨w.val, (show G.Adj b w.val from w.property).ne'⟩

private def withoutVertexToCut (u v : V) :
    withoutVertex G u →g G.deleteEdges {s(u, v)} where
  toFun := Subtype.val
  map_rel' := by
    intro x y h
    apply deleteEdges_adj.mpr
    refine ⟨h, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with hxy | hxy
    · exact x.property hxy.1
    · exact y.property hxy.2

/-- The side opposite `b` in the edge cut is exactly the corresponding branch of `G - b`. -/
private def cutSideEquivBranch (hT : G.IsTree) (b : V) (w : G.neighborSet b) :
    cutSide G b w.val ≃ (neighborBranch G b w).supp := by
  let D := G.deleteEdges {s(b, w.val)}
  let C := D.connectedComponentMk w.val
  have hb : ¬D.Reachable w.val b := fun h =>
    (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic w.property) h.symm
  have hne (x : cutSide G b w.val) : x.val ≠ b := by
    intro h
    have hr : D.Reachable w.val x.val := x.property
    rw [h] at hr
    exact hb hr
  have reach (x : V) (hx : x ≠ b) :
      D.Reachable w.val x ↔
        (withoutVertex G b).Reachable ⟨w.val, (show G.Adj b w.val from w.property).ne'⟩
          ⟨x, hx⟩ := by
    refine ⟨?_, fun h => h.map (withoutVertexToCut b w.val)⟩
    intro hr
    have hxC : x ∈ C := ConnectedComponent.sound hr.symm
    let lift : C.toSimpleGraph →g withoutVertex G b :=
      { toFun := fun y => ⟨y.val, hne ⟨y.val, (ConnectedComponent.exact y.property).symm⟩⟩
        map_rel' := by
          intro y z h
          change G.Adj y.val z.val
          exact deleteEdges_le _ (show D.Adj y.val z.val from h) }
    exact (C.reachable_toSimpleGraph ConnectedComponent.connectedComponentMk_mem hxC).map lift
  refine
    { toFun := fun x => ⟨⟨x.val, hne x⟩, ConnectedComponent.sound ((reach x.val (hne x)).mp
        x.property).symm⟩
      invFun := fun x => ⟨x.val.val, (reach x.val.val x.val.property).mpr
        (ConnectedComponent.exact x.property).symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Each component after vertex deletion contains a unique neighbor of the deleted vertex. -/
noncomputable def neighborEquivBranch (hT : G.IsTree) (b : V) :
    G.neighborSet b ≃ (withoutVertex G b).ConnectedComponent := by
  classical
  refine Equiv.ofBijective (neighborBranch G b) ⟨?_, ?_⟩
  · intro v w h
    by_contra hne
    have hvw : v.val ≠ w.val := fun he => hne (Subtype.ext he)
    have hreach := (ConnectedComponent.exact h).map (withoutVertexToCut b v.val)
    have hkeep : (G.deleteEdges {s(b, v.val)}).Adj b w.val := by
      refine deleteEdges_adj.mpr ⟨w.property, ?_⟩
      intro he
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with he | he
      · exact hvw he.2.symm
      · exact (show G.Adj b v.val from v.property).ne he.1
    exact (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic v.property)
      (hkeep.reachable.trans hreach.symm)
  · intro c
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨p, hp⟩ := hT.connected.preconnected.exists_isPath b x.val
    have hnil := p.not_nil_of_ne (Ne.symm x.property)
    have hbw := p.adj_snd hnil
    have htail : (p.tail.cons hbw).IsPath := by
      rw [p.cons_tail_eq hnil]
      exact hp
    have hb : b ∉ p.tail.support := ((Walk.cons_isPath_iff hbw p.tail).mp htail).2
    have hav (y : V) (hy : y ∈ p.tail.support) : y ∈ {z : V | z ≠ b} :=
      fun h => hb (h ▸ hy)
    exact ⟨⟨p.snd, hbw⟩, ConnectedComponent.sound (p.tail.induce _ hav).reachable⟩

private theorem cut_sides_card [Fintype V] (hT : G.IsTree) {u v : V} (huv : G.Adj u v) :
    Nat.card (cutSide G u v) + Nat.card (cutSide G v u) = Nat.card V := by
  classical
  let S := cutSide G u v
  have hCompl : Sᶜ = cutSide G v u := by
    ext x
    change (¬ (G.deleteEdges {s(u, v)}).Reachable v x) ↔
      (G.deleteEdges {s(v, u)}).Reachable u x
    rw [show s(v, u) = s(u, v) from Sym2.eq_swap]
    have hcover := deletedSide_cover hT.connected u v x
    have hdisj := Set.disjoint_left.mp
      (deletedSide_disjoint (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic huv))
    exact ⟨fun hn => hcover.resolve_right hn, fun h hh => hdisj h hh⟩
  rw [← hCompl, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.Set.sumCompl S)

private theorem even_cutSide_iff_odd_branch [Fintype V] (hT : G.IsTree)
    (hOdd : Odd (Nat.card V)) (b : V) (w : G.neighborSet b) :
    Even (Nat.card (cutSide G w.val b)) ↔ Odd (Nat.card (neighborBranch G b w).supp) := by
  rw [← Nat.card_congr (cutSideEquivBranch hT b w)]
  have hsum := cut_sides_card hT w.property
  rw [← hsum, Nat.odd_add] at hOdd
  exact hOdd.symm

private theorem even_card_odd_branches [Fintype V] (hT : G.IsTree)
    (hOdd : Odd (Nat.card V)) (b : V) :
    Even (Nat.card {w : G.neighborSet b // Odd (Nat.card (neighborBranch G b w).supp)}) := by
  classical
  let := Fintype.ofFinite (G.neighborSet b)
  let D := withoutVertex G b
  let e : (Σ w : G.neighborSet b, (neighborBranch G b w).supp) ≃ {x : V // x ≠ b} :=
    (Equiv.sigmaCongr (neighborEquivBranch hT b) (fun w => Equiv.refl _)).trans
      (Equiv.sigmaFiberEquiv D.connectedComponentMk)
  have hsum := Nat.card_congr e
  rw [Nat.card_sigma] at hsum
  have hsplit : Nat.card V = 1 + Nat.card {x : V // x ≠ b} := by
    rw [← Nat.card_congr (Equiv.sumCompl (· = b)), Nat.card_sum, Nat.card_unique]
  rw [hsplit, Nat.odd_add] at hOdd
  have hEvenSum : Even (∑ w : G.neighborSet b, Nat.card (neighborBranch G b w).supp) := by
    rw [hsum]
    simpa using hOdd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (Finset.even_sum_iff_even_card_odd _).mp hEvenSum

/-- On an odd-order tree, even indegrees are equivalent to directing precisely the
edges opposite odd branches into each vertex. -/
theorem even_indegrees_iff_odd_neighbor_branches [Fintype V] (hT : G.IsTree)
    (hOdd : Odd (Nat.card V)) (head : G.edgeSet → V) (hhead : ∀ e, head e ∈ e.val) :
    (∀ b, Even (indegree head b)) ↔
      ∀ b (w : G.neighborSet b),
        head ⟨s(w.val, b), G.adj_symm w.property⟩ = b ↔
          Odd (Nat.card (neighborBranch G b w).supp) := by
  classical
  constructor
  · intro heven b w
    exact (head_eq_iff_even_cutSide hT head hhead heven (G.adj_symm w.property)).trans
      (even_cutSide_iff_odd_branch hT hOdd b w)
  · intro hbranch b
    let B := {w : G.neighborSet b // Odd (Nat.card (neighborBranch G b w).supp)}
    let f (w : B) : {e : G.edgeSet // head e = b} :=
      ⟨⟨s(w.val.val, b), G.adj_symm w.val.property⟩, (hbranch b w.val).mpr w.property⟩
    have hinj : Function.Injective f := by
      intro w z h
      have he : s(w.val.val, b) = s(z.val.val, b) :=
        congrArg (fun e : {e : G.edgeSet // head e = b} => e.val.val) h
      exact Subtype.ext (Subtype.ext (Sym2.congr_left.mp he))
    have hsurj : Function.Surjective f := by
      intro e
      have hb := hhead e.val
      rw [e.property] at hb
      obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hb
      have hbw : G.Adj b w := by
        have he : s(b, w) ∈ G.edgeSet := hw ▸ e.val.property
        exact he
      let v : G.neighborSet b := ⟨w, hbw⟩
      have he : (⟨s(w, b), hbw.symm⟩ : G.edgeSet) = e.val :=
        Subtype.ext (Sym2.eq_swap.trans hw.symm)
      have hodd : Odd (Nat.card (neighborBranch G b v).supp) :=
        (hbranch b v).mp (he.symm ▸ e.property)
      exact ⟨⟨v, hodd⟩, Subtype.ext he⟩
    rw [indegree, ← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
    exact even_card_odd_branches hT hOdd b

/-- A finite odd-order tree has exactly one orientation with all indegrees even. -/
theorem existsUnique_even_indegree_head [Fintype V] (hT : G.IsTree)
    (hOdd : Odd (Nat.card V)) :
    ∃! head : G.edgeSet → V, (∀ e, head e ∈ e.val) ∧ ∀ b, Even (indegree head b) := by
  classical
  have hpar {u v : V} (huv : G.Adj u v) :
      Even (Nat.card (cutSide G u v)) ↔ ¬Even (Nat.card (cutSide G v u)) := by
    rw [Nat.not_even_iff_odd]
    rw [← cut_sides_card hT huv.symm, Nat.odd_add] at hOdd
    exact hOdd.symm
  have chooseHead (e : G.edgeSet) :
      ∃ v ∈ e.val, ∀ u ∈ e.val, u ≠ v → Even (Nat.card (cutSide G u v)) := by
    rcases e with ⟨⟨u, v⟩, huv⟩
    change G.Adj u v at huv
    change ∃ b ∈ s(u, v), ∀ a ∈ s(u, v), a ≠ b → Even (Nat.card (cutSide G a b))
    by_cases hv : Even (Nat.card (cutSide G u v))
    · refine ⟨v, Sym2.mem_iff.mpr (Or.inr rfl), ?_⟩
      intro a ha hne
      rcases Sym2.mem_iff.mp ha with rfl | rfl
      · exact hv
      · exact (hne rfl).elim
    · refine ⟨u, Sym2.mem_iff.mpr (Or.inl rfl), ?_⟩
      intro a ha hne
      rcases Sym2.mem_iff.mp ha with rfl | rfl
      · exact (hne rfl).elim
      · exact (hpar huv.symm).mpr hv
  choose head hhead hchoose using chooseHead
  have hcut {u v : V} (huv : G.Adj u v) :
      head ⟨s(u, v), huv⟩ = v ↔ Even (Nat.card (cutSide G u v)) := by
    let e : G.edgeSet := ⟨s(u, v), huv⟩
    change head e = v ↔ _
    rcases Sym2.mem_iff.mp (hhead e) with hu | hv
    · have heven := hchoose e v (Sym2.mem_iff.mpr (Or.inr rfl)) (hu ▸ huv.ne')
      rw [hu] at heven
      exact iff_of_false (fun hv => huv.ne (hu.symm.trans hv)) ((hpar huv.symm).mp heven)
    · have heven := hchoose e u (Sym2.mem_iff.mpr (Or.inl rfl)) (hv ▸ huv.ne)
      rw [hv] at heven
      exact iff_of_true hv heven
  have heven : ∀ b, Even (indegree head b) :=
    (even_indegrees_iff_odd_neighbor_branches hT hOdd head hhead).mpr fun b w =>
      (hcut (G.adj_symm w.property)).trans (even_cutSide_iff_odd_branch hT hOdd b w)
  refine ⟨head, ⟨hhead, heven⟩, ?_⟩
  intro other hother
  funext e
  rcases e with ⟨⟨u, v⟩, huv⟩
  change G.Adj u v at huv
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  change other e = head e
  have heq : other e = v ↔ head e = v :=
    (head_eq_iff_even_cutSide hT other hother.1 hother.2 huv).trans (hcut huv).symm
  rcases Sym2.mem_iff.mp (hother.1 e) with hu | hv
  · rcases Sym2.mem_iff.mp (hhead e) with hu' | hv'
    · exact hu.trans hu'.symm
    · exact (huv.ne (hu.symm.trans (heq.mpr hv'))).elim
  · exact hv.trans (heq.mp hv).symm

end

section

private abbrev Vertex (c m : ℕ) := Fin (c + 2) ⊕ Fin m

/-- A path with `c` internal vertices and `m` additional leaves at its first vertex. -/
private def stemAdj {c m : ℕ} : Vertex c m → Vertex c m → Prop
  | .inl i, .inl j => (pathGraph (c + 2)).Adj i j
  | .inl i, .inr _ => i = 0
  | .inr _, .inl j => j = 0
  | .inr _, .inr _ => False

private def stem (c m : ℕ) : SimpleGraph (Vertex c m) where
  Adj := stemAdj
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact h.symm
    all_goals exact h
  loopless := by
    constructor
    intro a
    cases a
    · exact (pathGraph _).loopless.irrefl _
    · exact id

private instance (c m : ℕ) : DecidableRel (stem c m).Adj :=
  fun a b => match a, b with
    | .inl i, .inl j => inferInstanceAs (Decidable ((pathGraph (c + 2)).Adj i j))
    | .inl i, .inr _ => inferInstanceAs (Decidable (i = 0))
    | .inr _, .inl j => inferInstanceAs (Decidable (j = 0))
    | .inr _, .inr _ => inferInstanceAs (Decidable False)

private def stemPathHom (c m : ℕ) : pathGraph (c + 2) →g stem c m where
  toFun := Sum.inl
  map_rel' h := h

private theorem stem_connected (c m : ℕ) : (stem c m).Connected := by
  have toRoot (a : Vertex c m) : (stem c m).Reachable a (.inl 0) := by
    cases a with
    | inl i => exact ((preconnected_pathGraph (c + 2)) i 0).map (stemPathHom c m)
    | inr j =>
      exact SimpleGraph.Adj.reachable (G := stem c m) (u := .inr j) (v := .inl 0) rfl
  exact (connected_iff _).mpr
    ⟨fun a b => (toRoot a).trans (toRoot b).symm, ⟨.inl 0⟩⟩

private def stemEdge (c m : ℕ) :
    (pathGraph (c + 2)).edgeSet ⊕ Fin m → (stem c m).edgeSet
  | .inl e => (stemPathHom c m).mapEdgeSet e
  | .inr j => ⟨s(.inl 0, .inr j), (mem_edgeSet _).mpr rfl⟩

private theorem stemEdge_surjective (c m : ℕ) : Function.Surjective (stemEdge c m) := by
  rintro ⟨⟨a, b⟩, he⟩
  have hab := (mem_edgeSet _).mp he
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      exact ⟨.inl ⟨s(i, j), (mem_edgeSet _).mpr hab⟩, rfl⟩
    | inr j =>
      change i = 0 at hab
      subst i
      exact ⟨.inr j, rfl⟩
  | inr i =>
    cases b with
    | inl j =>
      change j = 0 at hab
      subst j
      exact ⟨.inr i, Subtype.ext Sym2.eq_swap⟩
    | inr j =>
      exact False.elim hab

private theorem stem_isTree (c m : ℕ) : (stem c m).IsTree := by
  have hconn := stem_connected c m
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  have hge := Nat.card_le_card_of_surjective _ (stemEdge_surjective c m)
  rw [Nat.card_sum, Nat.card_fin] at hge
  have hpath : Nat.card (pathGraph (c + 2)).edgeSet + 1 = Nat.card (Fin (c + 2)) :=
    (isTree_iff_connected_and_card.mp (isTree_pathGraph_add_one (c + 1))).2
  rw [Nat.card_fin] at hpath
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin] at hle
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin]
  omega

private theorem stem_card_neighbors (c m : ℕ) (a : Vertex c m) :
    Nat.card ((stem c m).neighborSet a) = ((stem c m).neighborFinset a).card := by
  rw [Nat.card_eq_fintype_card, card_neighborFinset_eq_degree, card_neighborSet_eq_degree]

private theorem stem_card_root (c m : ℕ) :
    Nat.card ((stem c m).neighborSet (.inl 0)) = m + 1 := by
  let leaves : Finset (Vertex c m) := Finset.univ.map Function.Embedding.inr
  have h : (stem c m).neighborFinset (.inl 0) = insert (.inl 1) leaves := by
    ext a
    rw [mem_neighborFinset]
    cases a with
    | inl i =>
      change (pathGraph (c + 2)).Adj 0 i ↔ _
      rw [pathGraph_adj]
      simp only [Fin.val_zero, Nat.zero_add, Nat.add_one_ne_zero, or_false, Finset.mem_insert,
        Sum.inl.injEq, leaves, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.inr_apply, reduceCtorEq]
      simp only [Fin.ext_iff, Fin.val_one, exists_false, or_false]
      exact eq_comm
    | inr j =>
      change (0 : Fin (c + 2)) = 0 ↔ _
      simp [leaves]
  rw [stem_card_neighbors, h, Finset.card_insert_of_notMem (by simp [leaves])]
  simp [leaves]

private theorem stem_card_leaf (c m : ℕ) (j : Fin m) :
    Nat.card ((stem c m).neighborSet (.inr j)) = 1 := by
  have h : (stem c m).neighborFinset (.inr j) = {Sum.inl 0} := by
    ext a
    rw [mem_neighborFinset, Finset.mem_singleton]
    cases a with
    | inl i => change i = 0 ↔ Sum.inl i = Sum.inl 0; simp
    | inr i => change False ↔ Sum.inr i = Sum.inl 0; simp
  rw [stem_card_neighbors, h, Finset.card_singleton]

private theorem stem_card_tip (c m : ℕ) :
    Nat.card ((stem c m).neighborSet (.inl (Fin.last (c + 1)))) = 1 := by
  let prev : Fin (c + 2) := ⟨c, by omega⟩
  have h : (stem c m).neighborFinset (.inl (Fin.last (c + 1))) = {Sum.inl prev} := by
    ext a
    rw [mem_neighborFinset, Finset.mem_singleton]
    cases a with
    | inl i =>
      change (pathGraph (c + 2)).Adj (Fin.last (c + 1)) i ↔ _
      rw [pathGraph_adj]
      simp only [Fin.val_last, Sum.inl.injEq, Fin.ext_iff, prev]
      omega
    | inr i =>
      change Fin.last (c + 1) = 0 ↔ Sum.inr i = Sum.inl prev
      simp [Fin.ext_iff]
  rw [stem_card_neighbors, h, Finset.card_singleton]

private theorem stem_card_internal (c m : ℕ) (i : Fin c) :
    Nat.card ((stem c m).neighborSet (.inl i.castSucc.succ)) = 2 := by
  let prev : Fin (c + 2) := ⟨i, by omega⟩
  let next : Fin (c + 2) := ⟨i + 2, by omega⟩
  have h : (stem c m).neighborFinset (.inl i.castSucc.succ) =
      {Sum.inl prev, Sum.inl next} := by
    ext a
    rw [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    cases a with
    | inl j =>
      change (pathGraph (c + 2)).Adj i.castSucc.succ j ↔ _
      rw [pathGraph_adj]
      simp only [Fin.val_succ, Fin.val_castSucc, Sum.inl.injEq, Fin.ext_iff, prev, next]
      omega
    | inr j =>
      change i.castSucc.succ = 0 ↔ Sum.inr j = Sum.inl prev ∨ Sum.inr j = Sum.inl next
      simp [Fin.ext_iff]
  have hne : (Sum.inl prev : Vertex c m) ∉ ({Sum.inl next} : Finset (Vertex c m)) := by
    simp [Fin.ext_iff, prev, next]
  rw [stem_card_neighbors, h, Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-- The first summand labels the two endpoints and the additional leaves.
The second summand labels the internal vertices of the path. -/
private def place (c m : ℕ) : Fin (m + 2) ⊕ Fin c → Vertex c m
  | .inl i => Fin.cases (.inl 0) (Fin.cases (.inl (Fin.last (c + 1))) Sum.inr) i
  | .inr i => .inl i.castSucc.succ

private theorem place_injective (c m : ℕ) : Function.Injective (place c m) := by
  have zero_ne_tip : (0 : Fin (c + 2)) ≠ Fin.last (c + 1) := by simp [Fin.ext_iff]
  have zero_ne_inside (i : Fin c) : (0 : Fin (c + 2)) ≠ i.castSucc.succ := by
    simp [Fin.ext_iff]
  have tip_ne_inside (i : Fin c) : Fin.last (c + 1) ≠ i.castSucc.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hv
    omega
  intro a b
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      refine Fin.cases ?_ (Fin.cases ?_ ?_) i <;>
        refine Fin.cases ?_ (Fin.cases ?_ ?_) j <;>
        simp only [place, Fin.cases_zero, Fin.cases_succ, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq, zero_ne_tip, Ne.symm zero_ne_tip, Fin.succ_inj, true_implies, false_implies] <;> simp
    | inr j =>
      refine Fin.cases ?_ (Fin.cases ?_ ?_) i <;>
        simp only [place, Fin.cases_zero, Fin.cases_succ, Sum.inl.injEq, reduceCtorEq,
          zero_ne_inside, tip_ne_inside, false_implies]
      simp
  | inr i =>
    cases b with
    | inl j =>
      refine Fin.cases ?_ (Fin.cases ?_ ?_) j <;>
        simp only [place, Fin.cases_zero, Fin.cases_succ, Sum.inl.injEq, reduceCtorEq,
          Ne.symm (zero_ne_inside i), Ne.symm (tip_ne_inside i), false_implies]
      simp
    | inr j =>
      simp [place, Fin.ext_iff]

private noncomputable def placeEquiv (c m : ℕ) : Fin (m + 2) ⊕ Fin c ≃ Vertex c m :=
  Equiv.ofBijective (place c m) <| (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨place_injective c m, by simp [Fintype.card_sum]; omega⟩

private theorem stem_odd_place_left {c m : ℕ} (hm : Even m) (i : Fin (m + 2)) :
    Odd (Nat.card ((stem c m).neighborSet (place c m (.inl i)))) := by
  refine Fin.cases ?_ (Fin.cases ?_ ?_) i
  · simp only [place, Fin.cases_zero, stem_card_root]
    have := Nat.even_iff.mp hm
    exact Nat.odd_iff.mpr (by omega)
  · rw [show place c m (.inl (0 : Fin (m + 1)).succ) = .inl (Fin.last (c + 1)) from rfl,
      stem_card_tip]
    decide
  · intro j
    rw [show place c m (.inl j.succ.succ) = .inr j from rfl, stem_card_leaf]
    decide

private theorem stem_not_odd_place_right (c m : ℕ) (i : Fin c) :
    ¬ Odd (Nat.card ((stem c m).neighborSet (place c m (.inr i)))) := by
  rw [show place c m (.inr i) = .inl i.castSucc.succ from rfl, stem_card_internal]
  decide

/-- Every nonempty even set of labels is the set of odd-degree vertices of a tree.
The witness also supplies a decision procedure for its adjacency relation. -/
theorem exists_isTree_odd_neighborSet_card {B : Type*} [Finite B]
    (S : Finset B) (hne : S.Nonempty) (heven : Even S.card) :
    ∃ T : SimpleGraph B,
      T.IsTree ∧ ∀ b : B, Odd (Nat.card (T.neighborSet b)) ↔ b ∈ S := by
  classical
  let _ := Fintype.ofFinite B
  let m := S.card - 2
  have hsize : S.card = m + 2 := by
    have := Finset.card_pos.mpr hne
    have := Nat.even_iff.mp heven
    dsimp [m]
    omega
  have hm : Even m := by
    have := Nat.even_iff.mp heven
    exact Nat.even_iff.mpr (by omega)
  let c := Fintype.card {b : B // b ∉ S}
  let sLabel : {b : B // b ∈ S} ≃ Fin (m + 2) :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans hsize)
  let otherLabel : {b : B // b ∉ S} ≃ Fin c := Fintype.equivFin _
  let label : B ≃ Vertex c m :=
    ((Equiv.sumCompl (· ∈ S)).symm.trans (Equiv.sumCongr sLabel otherLabel)).trans
      (placeEquiv c m)
  let T := (stem c m).comap label
  let iso : T ≃g stem c m := Iso.comap label _
  refine ⟨T, iso.isTree_iff.mpr (stem_isTree c m), ?_⟩
  intro b
  rw [Nat.card_congr (iso.mapNeighborSet b)]
  change Odd (Nat.card ((stem c m).neighborSet (label b))) ↔ b ∈ S
  by_cases hb : b ∈ S
  · refine iff_of_true ?_ hb
    unfold label
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hb]
    exact stem_odd_place_left hm (sLabel ⟨b, hb⟩)
  · refine iff_of_false ?_ hb
    unfold label
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hb]
    exact stem_not_odd_place_right c m (otherLabel ⟨b, hb⟩)

end

end D5.S3.Combinatorics.Graph.Incidence.TreeParity
