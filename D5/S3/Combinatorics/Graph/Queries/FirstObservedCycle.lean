/- GID: D5/S3/Combinatorics/Graph/Queries/FirstObservedCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/FirstObservedCycle
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: The first observed cycle comes from a new edge between known unqueried vertices. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Lattice.Fold

/-! Cycle detection by complete-neighborhood queries in a rooted exploration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph

namespace D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle

variable {V : Type*}

/-- Retain precisely the edges incident to a vertex whose neighborhood was queried. -/
def exposed (G : SimpleGraph V) (queried : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∈ queried ∨ y ∈ queried)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

private theorem exposed_mono (G : SimpleGraph V) {Q R : Set V} (h : Q ⊆ R) :
    exposed G Q ≤ exposed G R :=
  fun _ _ ha => ⟨ha.1, ha.2.imp (fun hq => h hq) (fun hq => h hq)⟩

private theorem star_adj (x a b : V) (T : Finset V) :
    (T.sup (SimpleGraph.edge x)).Adj a b ↔ ∃ y ∈ T, (SimpleGraph.edge x y).Adj a b := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert u s hs ih =>
    rw [Finset.sup_insert, SimpleGraph.sup_adj, ih]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨u, Finset.mem_insert_self _ _, h⟩
      · exact ⟨y, Finset.mem_insert_of_mem hy, h⟩
    · rintro ⟨y, hy, h⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h⟩

private theorem reachable_eq_of_isolated {G : SimpleGraph V} {x y : V}
    (hiso : ∀ v, ¬ G.Adj y v) (hreach : G.Reachable x y) : x = y := by
  obtain ⟨p⟩ := hreach.symm
  cases p with
  | nil => rfl
  | cons ha _ => exact (hiso _ ha).elim

private theorem acyclic_add_isolated_star (H : SimpleGraph V) (x : V) (T : Finset V)
    (hx : x ∉ T) (hiso : ∀ y ∈ T, ∀ v, ¬ H.Adj y v) (hH : H.IsAcyclic) :
    (H ⊔ T.sup (SimpleGraph.edge x)).IsAcyclic := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa
  | @insert y U hy ih =>
    have hxU : x ∉ U := fun h => hx (Finset.mem_insert_of_mem h)
    have hxy : x ≠ y := fun h => hx (h ▸ Finset.mem_insert_self _ _)
    have hHU : (H ⊔ U.sup (SimpleGraph.edge x)).IsAcyclic :=
      ih hxU (fun y h => hiso y (Finset.mem_insert_of_mem h))
    have hY (v : V) : ¬ (H ⊔ U.sup (SimpleGraph.edge x)).Adj y v := by
      rw [SimpleGraph.sup_adj, star_adj]
      rintro (ha | ⟨z, hz, ha⟩)
      · exact hiso y (Finset.mem_insert_self _ _) v ha
      · rw [SimpleGraph.edge_adj] at ha
        rcases ha.1 with h | h
        · exact hxy h.1.symm
        · exact hy (h.1.symm ▸ hz)
    have hnr : ¬ (H ⊔ U.sup (SimpleGraph.edge x)).Reachable x y :=
      fun h => hxy (reachable_eq_of_isolated hY h)
    rw [Finset.sup_insert, sup_left_comm, sup_comm (SimpleGraph.edge x y)]
    exact hHU.sup_edge_of_not_reachable hnr

private theorem first_cycle_iff_exists_known_neighbor [Finite V] (G : SimpleGraph V)
    (Q : Set V) (x : V) (hx : x ∉ Q)
    (hconn : ∀ q ∈ Q, (exposed G Q).Reachable x q)
    (hforest : (exposed G Q).IsAcyclic) :
    ¬ (exposed G (insert x Q)).IsAcyclic ↔
      ∃ y, G.Adj x y ∧ y ∉ Q ∧ (exposed G Q).Reachable x y := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let H := exposed G Q
  let H' := exposed G (insert x Q)
  let T := Finset.univ.filter (fun y => G.Adj x y ∧ y ∉ Q)
  have hT (y : V) : y ∈ T ↔ G.Adj x y ∧ y ∉ Q := by simp [T]
  have hstep : H' = H ⊔ T.sup (SimpleGraph.edge x) := by
    ext a b
    rw [SimpleGraph.sup_adj, star_adj]
    change (G.Adj a b ∧ (a ∈ insert x Q ∨ b ∈ insert x Q)) ↔
      (G.Adj a b ∧ (a ∈ Q ∨ b ∈ Q)) ∨ ∃ y ∈ T, (SimpleGraph.edge x y).Adj a b
    simp only [Set.mem_insert_iff]
    constructor
    · rintro ⟨ha, hab⟩
      by_cases hQ : a ∈ Q ∨ b ∈ Q
      · exact Or.inl ⟨ha, hQ⟩
      · rcases hab with (rfl | haQ) | (rfl | hbQ)
        · exact Or.inr ⟨b, (hT b).mpr ⟨ha, fun hbQ => hQ (Or.inr hbQ)⟩,
            (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, ha.ne⟩⟩
        · exact (hQ (Or.inl haQ)).elim
        · exact Or.inr ⟨a, (hT a).mpr ⟨ha.symm, fun haQ => hQ (Or.inl haQ)⟩,
            (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, ha.ne⟩⟩
        · exact (hQ (Or.inr hbQ)).elim
    · rintro (⟨ha, haQ | hbQ⟩ | ⟨y, hyT, hy⟩)
      · exact ⟨ha, Or.inl (Or.inr haQ)⟩
      · exact ⟨ha, Or.inr (Or.inr hbQ)⟩
      · rw [SimpleGraph.edge_adj] at hy
        rcases hy.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · subst a
          subst b
          exact ⟨((hT y).1 hyT).1, Or.inl (Or.inl rfl)⟩
        · subst a
          subst b
          exact ⟨((hT y).1 hyT).1.symm, Or.inr (Or.inl rfl)⟩
  constructor
  · intro hcycle
    by_contra hn
    apply hcycle
    change H'.IsAcyclic
    rw [hstep]
    apply acyclic_add_isolated_star H x T (fun ht => G.loopless.irrefl _ ((hT x).mp ht).1) _ hforest
    intro y hy v hEdge
    have hReach : H.Reachable x y := by
      rcases hEdge.2 with hyQ | hvQ
      · exact hconn y hyQ
      · exact (hconn v hvQ).trans hEdge.symm.reachable
    obtain ⟨hyG, hyQ⟩ := (hT y).mp hy
    exact hn ⟨y, hyG, hyQ, hReach⟩
  · rintro ⟨y, hyG, hyQ, hreach⟩ hacyclic
    have hle : H ⊔ SimpleGraph.edge x y ≤ H' := by
      rw [hstep]
      exact sup_le_sup_left (Finset.le_sup (f := SimpleGraph.edge x) ((hT y).mpr ⟨hyG, hyQ⟩)) H
    have ha := (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff.mp (hacyclic.anti hle)).2 hreach
    rcases ha with he | ha
    · exact hyG.ne he
    · exact ha.2.elim hx hyQ

/-- The queried set grows by queries reachable through edges already exposed from the root. -/
inductive RootedExploration (G : SimpleGraph V) (root : V) : Set V → Prop where
  | start : RootedExploration G root ∅
  | step {Q : Set V} {x : V} :
      RootedExploration G root Q → (exposed G Q).Reachable root x →
      RootedExploration G root (insert x Q)

private theorem connected_to_queries {G : SimpleGraph V} {root : V} {Q : Set V}
    (history : RootedExploration G root Q) :
    ∀ v ∈ Q, (exposed G Q).Reachable root v := by
  induction history with
  | start => simp
  | @step Q x _ hx ih =>
    have hle := exposed_mono G (Set.subset_insert x Q)
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | h
    · exact hx.mono hle
    · exact (ih v h).mono hle

/-- Exposing a first cycle requires a new edge to an already known unqueried vertex. -/
theorem first_observed_cycle [Finite V] (G : SimpleGraph V)
    (root x : V) (Q : Set V) (history : RootedExploration G root Q)
    (known : (exposed G Q).Reachable root x) (forest : (exposed G Q).IsAcyclic) :
    let queriedAfter := insert x Q
    ¬ (exposed G queriedAfter).IsAcyclic ↔ x ∉ Q ∧
      ∃ y, G.Adj x y ∧ y ∉ Q ∧ (exposed G Q).Reachable root y := by
  classical
  dsimp only
  by_cases hx : x ∈ Q
  · simp [hx, Set.insert_eq_of_mem hx, forest]
  have hconn (v : V) (hv : v ∈ Q) : (exposed G Q).Reachable x v :=
    known.symm.trans (connected_to_queries history v hv)
  rw [first_cycle_iff_exists_known_neighbor G Q x hx hconn forest]
  simp only [hx, not_false_eq_true, true_and]
  exact exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ =>
    ⟨known.trans, known.symm.trans⟩

end D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle
