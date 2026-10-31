/- GID: D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks
   mirror-E: none(waiver:consumed-chronological-pruning-helper)
   anchors: []
   utility: none
   digest: Chronological degree-one deletion leaves forests with unique component boundaries. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Finite.Lemmas

/-! Generic deletion-rank facts consumed by actual finite-flag pruning. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi

namespace Pruning

/-- Chronological deletion ranks: before the cut, a vertex has at most one
neighbor still present. Equal ranks are counted as present. -/
structure LeafRanks {V : Type} (G : SimpleGraph V) where
  rank : V → ℕ
  cut : ℕ
  later_unique : ∀ v, rank v < cut → ∀ a b, G.Adj v a → G.Adj v b →
    rank v ≤ rank a → rank v ≤ rank b → a = b

private theorem acyclic_of_unique_later {V : Type} (G : SimpleGraph V) (rank : V → ℕ)
    (hu : ∀ v a b, G.Adj v a → G.Adj v b → rank v ≤ rank a → rank v ≤ rank b → a = b) :
    G.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {z | z ∈ c.support} rank
    c.support.finite_toSet ⟨v, c.start_mem_support⟩
  let q := c.rotate m hm
  have hq : q.IsCycle := hc.rotate hm
  have hs : q.snd ∈ c.support :=
    (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support 1)
  have hp : q.penultimate ∈ c.support :=
    (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support (q.length - 1))
  exact hq.snd_ne_penultimate (hu m q.snd q.penultimate
    (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm
    (hmin _ hs) (hmin _ hp))

theorem deleted_acyclic {V : Type} {G : SimpleGraph V} (P : LeafRanks G) :
    (G.induce {v | P.rank v < P.cut}).IsAcyclic := by
  apply acyclic_of_unique_later _ (fun v => P.rank v.val)
  intro v a b ha hb hra hrb
  exact Subtype.ext (P.later_unique v.val v.property a.val b.val ha hb hra hrb)

theorem cycle_retained {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    ∀ w ∈ c.support, P.cut ≤ P.rank w := by
  classical
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {z | z ∈ c.support} P.rank
    c.support.finite_toSet ⟨v, c.start_mem_support⟩
  have hkeep : P.cut ≤ P.rank m := by
    by_contra hd
    let q := c.rotate m hm
    have hq : q.IsCycle := hc.rotate hm
    have hs : q.snd ∈ c.support :=
      (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support 1)
    have hp : q.penultimate ∈ c.support :=
      (c.mem_support_rotate_iff m hm).mp (q.getVert_mem_support (q.length - 1))
    exact hq.snd_ne_penultimate (P.later_unique m (by omega) q.snd q.penultimate
      (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm
      (hmin _ hs) (hmin _ hp))
  exact fun w hw => hkeep.trans (hmin w hw)

/-- A path between retained vertices cannot dip into a deleted vertex: a
minimum-rank internal vertex would have two distinct later neighbors. -/
theorem retained_path {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hu : P.cut ≤ P.rank u) (hv : P.cut ≤ P.rank v) :
    ∀ w ∈ p.support, P.cut ≤ P.rank w := by
  classical
  intro w hw
  by_contra hbad
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {z | z ∈ p.support} P.rank
    p.support.finite_toSet ⟨u, p.start_mem_support⟩
  have hdel : P.rank m < P.cut := lt_of_le_of_lt (hmin w hw) (by omega)
  obtain ⟨l, r, hl, hr, happ⟩ := hp.mem_support_iff_exists_append.mp hm
  have hln : ¬l.Nil := by
    intro hnil
    have heq := hnil.eq
    subst m
    omega
  have hrn : ¬r.Nil := by
    intro hnil
    have heq := hnil.eq
    subst v
    omega
  have hal : l.penultimate ∈ p.support := by
    rw [happ]
    exact l.support_subset_support_append_left r (l.getVert_mem_support _)
  have hbr : r.snd ∈ p.support := by
    rw [happ]
    exact l.support_subset_support_append_right r (r.getVert_mem_support 1)
  have heq := P.later_unique m hdel l.penultimate r.snd
    (l.adj_penultimate hln).symm (r.adj_snd hrn) (hmin _ hal) (hmin _ hbr)
  have hne := (happ ▸ hp).ne_of_mem_support_of_append
    (r.adj_snd hrn).ne' (l.getVert_mem_support (l.length - 1)) (r.getVert_mem_support 1)
  exact hne heq

theorem retained_connected {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    (hc : G.Connected) (hne : ∃ v, P.cut ≤ P.rank v) :
    (G.induce {v | P.cut ≤ P.rank v}).Connected := by
  classical
  let : Nonempty {v | P.cut ≤ P.rank v} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  obtain ⟨p, hp⟩ := hc.exists_isPath u.val v.val
  exact (p.induce _ (retained_path P p hp u.property v.property)).reachable

private theorem boundary_walk {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {u v : V} (p : G.Walk u v) : p.IsPath →
    (∀ w ∈ p.support, P.rank w < P.cut) → ∀ a b,
    G.Adj u a → G.Adj v b → P.rank u ≤ P.rank a → P.cut ≤ P.rank b →
    a ∉ p.support → u = v ∧ a = b := by
  classical
  induction p with
  | @nil u =>
    intro hp hall a b ha hb hra hrb hnot
    exact ⟨rfl, P.later_unique u (hall u (by simp)) a b ha hb hra (by
      have := hall u (by simp)
      omega)⟩
  | @cons u v w huv p ih =>
    intro hp hall a b ha hb hra hrb hnot
    have hparts := (SimpleGraph.Walk.cons_isPath_iff huv p).mp hp
    have hu : P.rank u < P.cut := hall u (by simp)
    have hdesc : P.rank v < P.rank u := by
      by_contra hh
      have heq := P.later_unique u hu a v ha huv hra (by omega)
      exact hnot (by simp [heq, p.start_mem_support])
    have hrec := ih hparts.1 (fun z hz => hall z (by simp [hz]))
      u b huv.symm hb (le_of_lt hdesc) hrb hparts.2
    have hbdel : P.rank b < P.cut := hrec.2 ▸ hu
    omega

private theorem boundary_exists {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {u v : V} (p : G.Walk u v) : P.rank u < P.cut → P.cut ≤ P.rank v →
    ∃ x y, ∃ q : G.Walk u x, (∀ z ∈ q.support, P.rank z < P.cut) ∧
      G.Adj x y ∧ P.cut ≤ P.rank y := by
  classical
  induction p with
  | nil => intro hu hv; omega
  | @cons u v w huv p ih =>
    intro hu hw
    by_cases hv : P.cut ≤ P.rank v
    · exact ⟨u, v, .nil, by simpa using hu, huv, hv⟩
    · obtain ⟨x, y, q, hq, hxy, hy⟩ := ih (by omega) hw
      refine ⟨x, y, .cons huv q, ?_, hxy, hy⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · exact hq z hz

abbrev DeletedGraph {V : Type} {G : SimpleGraph V} (P : LeafRanks G) :=
  G.induce {v | P.rank v < P.cut}

structure ComponentBoundary {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    (c : (DeletedGraph P).ConnectedComponent) where
  inside : {v | P.rank v < P.cut}
  inside_mem : inside ∈ c
  outside : V
  outside_retained : P.cut ≤ P.rank outside
  adjacent : G.Adj inside.val outside

theorem component_boundary_unique {V : Type} {G : SimpleGraph V} (P : LeafRanks G)
    {c : (DeletedGraph P).ConnectedComponent} (A B : ComponentBoundary P c) :
    A.inside.val = B.inside.val ∧ A.outside = B.outside := by
  classical
  let p := (c.reachable_of_mem_supp A.inside_mem B.inside_mem).some.toPath
  let φ : DeletedGraph P →g G :=
    (SimpleGraph.Embedding.induce {v | P.rank v < P.cut}).toHom
  have hp : (p.val.map φ).IsPath :=
    p.property.map (SimpleGraph.Embedding.induce (G := G) _).injective
  have hall : ∀ z ∈ (p.val.map φ).support, P.rank z < P.cut := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact w.property
  apply boundary_walk P (p.val.map φ) hp hall A.outside B.outside A.adjacent B.adjacent
  · change P.rank A.inside.val ≤ P.rank A.outside
    have hd : P.rank A.inside.val < P.cut := A.inside.property
    have := A.outside_retained
    omega
  · exact B.outside_retained
  · intro hm
    have := hall A.outside hm
    have := A.outside_retained
    omega

theorem component_boundary_nonempty {V : Type} {G : SimpleGraph V}
    (P : LeafRanks G) (hc : G.Connected) (hk : ∃ v, P.cut ≤ P.rank v)
    (c : (DeletedGraph P).ConnectedComponent) : Nonempty (ComponentBoundary P c) := by
  classical
  obtain ⟨u, hu⟩ := c.nonempty_supp
  obtain ⟨k, hk⟩ := hk
  obtain ⟨x, y, q, hq, hxy, hy⟩ :=
    boundary_exists P (hc u.val k).some u.property hk
  have hx := hq x q.end_mem_support
  have hmem : (⟨x, hx⟩ : {v | P.rank v < P.cut}) ∈ c := by
    have heq := SimpleGraph.ConnectedComponent.sound (q.induce _ hq).reachable
    change (DeletedGraph P).connectedComponentMk ⟨x, hx⟩ = c
    exact heq.symm.trans hu
  exact ⟨⟨⟨x, hx⟩, hmem, y, hy, hxy⟩⟩

end Pruning

end D5.S3.Combinatorics.Graph.Jacobi
