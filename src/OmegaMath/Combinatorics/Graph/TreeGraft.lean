import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.GraphDistance
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

/-! Omega original. Distances after moving a terminal leaf in a tree. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph

section MovingLeaf

namespace OmegaMath.TreeGraft

variable {V : Type*}

/-- The vertices left after deleting the moved tip. -/
abbrev Surviving (z : V) := {v : V // v ≠ z}

/-- The induced graph on the surviving carrier. -/
abbrev surviving (T : SimpleGraph V) (z : V) : SimpleGraph (Surviving z) :=
  T.induce {v | v ≠ z}

/-- Move the unique edge at `z` to a new attachment point `r`. -/
def graft (T : SimpleGraph V) (z r : V) : SimpleGraph V :=
  T.deleteIncidenceSet z ⊔ SimpleGraph.edge z r

section Metric

variable {T : SimpleGraph V} {z l r : V}

theorem leaf_subsingleton (h : ∀ v, T.Adj z v ↔ v = l) :
    (T.neighborSet z).Subsingleton :=
  fun _ hu _ hv => ((h _).mp hu).trans ((h _).mp hv).symm

private theorem surviving_connected (hT : T.Connected) (hz : (T.neighborSet z).Subsingleton)
    (l' : Surviving z) : (surviving T z).Connected := by
  let : Nonempty (Surviving z) := ⟨l'⟩
  refine ⟨hT.preconnected.induce_of_degree_eq_one ?_⟩
  intro v hv
  have : v = z := by simpa using hv
  subst v
  exact hz

private theorem surviving_isTree (hT : T.IsTree) (hz : (T.neighborSet z).Subsingleton)
    (l' : Surviving z) : (surviving T z).IsTree :=
  ⟨surviving_connected hT.connected hz l', hT.isAcyclic.induce _⟩

/-- A shortest path between survivors can be taken entirely in the induced graph. -/
theorem surviving_dist (hT : T.Connected) (hz : (T.neighborSet z).Subsingleton)
    (u v : Surviving z) : (surviving T z).dist u v = T.dist u.val v.val := by
  obtain ⟨p, hp, hpLen⟩ := hT.exists_path_of_dist u.val v.val
  have hsupport : ∀ x ∈ p.support, x ≠ z := by
    intro x hx heq
    subst x
    exact hp.isTrail.notMem_support_of_subsingleton_neighborSet u.property.symm v.property.symm hz hx
  let q := p.induce {v | v ≠ z} hsupport
  have hlen : q.length = p.length := by
    rw [← Walk.length_map (Embedding.induce (G := T) _).toHom q]
    simp [q]
  apply le_antisymm
  · calc
      (surviving T z).dist u v ≤ q.length := dist_le q
      _ = T.dist u.val v.val := hlen.trans hpLen
  · obtain ⟨p', hp'⟩ := (surviving_connected hT hz u).exists_walk_length_eq_dist u v
    calc
      T.dist u.val v.val ≤ (p'.map (Embedding.induce (G := T) _).toHom).length :=
        dist_le _
      _ = (surviving T z).dist u v := by rw [Walk.length_map, hp']

/-- Every shortest walk from the moved tip starts with the unique leaf edge. -/
theorem leaf_dist (hT : T.Connected) (hz : ∀ v, T.Adj z v ↔ v = l)
    (l' : Surviving z) (hl : l'.val = l) (v : Surviving z) :
    T.dist z v.val = 1 + (surviving T z).dist l' v := by
  rw [surviving_dist hT (leaf_subsingleton hz), hl]
  have hzl : T.Adj z l := (hz l).mpr rfl
  apply le_antisymm
  · rw [← dist_eq_one_iff_adj.mpr hzl]
    exact hT.dist_triangle
  · suffices ∀ y, y ≠ z → 1 + T.dist l y ≤ T.dist z y from this v.val v.property
    intro y hy
    obtain ⟨p, hp⟩ := hT.exists_walk_length_eq_dist z y
    cases p with
    | nil => exact (hy rfl).elim
    | @cons _ w _ hadj tail =>
      have : w = l := (hz _).mp hadj
      subst w
      have htail := T.dist_le tail
      simp only [Walk.length_cons] at hp
      omega

@[simp] theorem graft_adj_leaf (hn : r ≠ z) (v : V) :
    (graft T z r).Adj z v ↔ v = r := by
  simp [graft, sup_adj, deleteIncidenceSet_adj, edge_adj, Ne.symm hn]
  rintro rfl
  exact hn.symm

/-- For a leaf, the removal in the move deletes exactly the old attachment edge. -/
private theorem graft_eq_delete_edge (h : ∀ v, T.Adj z v ↔ v = l) :
    graft T z r = T.deleteEdges {s(z, l)} ⊔ SimpleGraph.edge z r := by
  have hi : T.incidenceSet z = {s(z, l)} := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      constructor
      · intro he
        obtain ⟨huv, rfl | rfl⟩ := T.mk'_mem_incidenceSet_iff.mp he
        · rw [(h v).mp huv]
          rfl
        · rw [(h u).mp huv.symm, Sym2.eq_swap]
          rfl
      · intro he
        rw [Set.mem_singleton_iff.mp he]
        exact T.mk'_mem_incidenceSet_left_iff.mpr ((h l).mpr rfl)
  rw [graft, deleteIncidenceSet, hi]

@[simp] theorem surviving_graft : surviving (graft T z r) z = surviving T z := by
  ext u v
  change (graft T z r).Adj u.val v.val ↔ T.Adj u.val v.val
  simp [graft, sup_adj, deleteIncidenceSet_adj, edge_adj, u.property, v.property]

private theorem graft_isTree (hT : T.IsTree) (hz : (T.neighborSet z).Subsingleton) (hr : r ≠ z) :
    (graft T z r).IsTree := by
  have hU := surviving_connected hT.connected hz ⟨r, hr⟩
  have hreach : ∀ v, (graft T z r).Reachable v r := by
    intro v
    by_cases hv : v = z
    · subst v
      exact ((graft_adj_leaf hr r).mpr rfl).reachable
    · have h := hU ⟨v, hv⟩ ⟨r, hr⟩
      rw [← surviving_graft (T := T) (r := r)] at h
      exact h.map (Embedding.induce _).toHom
  let : Nonempty V := ⟨z⟩
  refine ⟨⟨fun u v => (hreach u).trans (hreach v).symm⟩, ?_⟩
  have hno : ¬ (T.deleteIncidenceSet z).Reachable z r := by
    rintro ⟨p⟩
    cases p with
    | nil => exact hr rfl
    | cons h _ => simp [deleteIncidenceSet_adj] at h
  exact (hT.isAcyclic.anti (deleteIncidenceSet_le T z)).sup_edge_of_not_reachable hno

theorem graft_dist_surviving (hT : T.IsTree) (hz : ∀ v, T.Adj z v ↔ v = l)
    (r' : Surviving z) (u v : Surviving z) :
    (graft T z r'.val).dist u.val v.val = (surviving T z).dist u v ∧
      T.dist u.val v.val = (surviving T z).dist u v := by
  have hH := graft_isTree hT (leaf_subsingleton hz) r'.property
  refine ⟨?_, (surviving_dist hT.connected (leaf_subsingleton hz) u v).symm⟩
  rw [← surviving_dist hH.connected (leaf_subsingleton (graft_adj_leaf r'.property)) u v,
    surviving_graft]

end Metric
end OmegaMath.TreeGraft

end MovingLeaf

section Paths

namespace OmegaMath.TreeGraft

variable {V : Type*} [Fintype V]

theorem path_walk_length_bound {n : ℕ} {i j : Fin n} (p : (pathGraph n).Walk i j) :
    j.val ≤ i.val + p.length ∧ i.val ≤ j.val + p.length := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
      have h := SimpleGraph.pathGraph_adj.mp hadj
      simp only [Walk.length_cons]
      omega

theorem dist_lt_card (G : SimpleGraph V) (hc : G.Connected) (i j : V) :
    G.dist i j < Fintype.card V := by
  obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist i j
  rw [← hlen]
  exact hp.length_lt

omit [Fintype V] in
theorem dist_eq_index_of_shortest {G : SimpleGraph V} (hc : G.Connected)
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v) (i : ℕ)
    (hi : i ≤ p.length) : G.dist u (p.getVert i) = i := by
  have htake := G.dist_le (p.take i)
  have hdrop := G.dist_le (p.drop i)
  simp only [Walk.take_length, inf_eq_left.mpr hi] at htake
  simp only [Walk.drop_length] at hdrop
  have ht := (hc.preconnected u (p.getVert i)).dist_triangle_left v
  omega

theorem path_iso_of_dist_max (G : SimpleGraph V) (hc : G.Connected) {u v : V}
    (hd : G.dist u v + 1 = Fintype.card V) :
    Nonempty (pathGraph (Fintype.card V) ≃g G) := by
  obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist u v
  have hcard : p.length + 1 = Fintype.card V := by omega
  let f : Fin (Fintype.card V) → V := fun i => p.getVert i
  have hidx (i : Fin (Fintype.card V)) : G.dist u (f i) = i.val :=
    dist_eq_index_of_shortest hc p hlen i (by have := i.isLt; omega)
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    rw [← hidx i, hij, hidx j]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, Fintype.card_fin _⟩
  let e := Equiv.ofBijective f hbij
  refine ⟨{ __ := e, map_rel_iff' := ?_ }⟩
  intro i j
  change G.Adj (f i) (f j) ↔ (pathGraph (Fintype.card V)).Adj i j
  rw [SimpleGraph.pathGraph_adj]
  constructor
  · intro hadj
    have hdiff := hadj.diff_dist_adj (u := u)
    rw [hidx i, hidx j] at hdiff
    have hne : i.val ≠ j.val := fun he => hadj.ne (congrArg f (Fin.ext he))
    omega
  · rintro (hij | hji)
    · have hi : i.val < p.length := by have := j.isLt; omega
      change G.Adj (p.getVert i.val) (p.getVert j.val)
      rw [← hij]
      exact p.adj_getVert_succ hi
    · have hj : j.val < p.length := by have := i.isLt; omega
      change G.Adj (p.getVert i.val) (p.getVert j.val)
      rw [← hji]
      exact (p.adj_getVert_succ hj).symm

variable {W : Type*}

omit [Fintype V] in
private theorem edist_le_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (u v : V) : H.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · simp [h]
  · obtain ⟨p, hp⟩ := (SimpleGraph.reachable_of_edist_ne_top h).exists_walk_length_eq_edist
    rw [← hp, ← p.length_map f.toHom]
    exact SimpleGraph.edist_le _

omit [Fintype V] in
theorem edist_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (i j : V) :
    G.edist i j = H.edist (e i) (e j) :=
  le_antisymm (by simpa using edist_le_of_iso e.symm (e i) (e j)) (edist_le_of_iso e i j)

end OmegaMath.TreeGraft

end Paths

section Arms

namespace OmegaMath.TreeGraft

variable {V : Type*} {T : SimpleGraph V} {z : V} {L : ℕ}

/-- The two pendant arms, indexed along the path left after removing the shorter
tip. The original arm lengths are `L - root.val` and `root.val + 1`. -/
structure TerminalArms [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (z : V) (L : ℕ) where
  q : Fin (L + 1) ↪ Surviving z
  root : Fin (L + 1)
  shorter : 2 * root.val < L
  step : ∀ i j, i.val + 1 = j.val → T.Adj (q i).val (q j).val
  tip_adj : T.Adj z (q 0).val
  tip_degree : T.degree z = 1
  long_degree : T.degree (q (Fin.last L)).val = 1
  internal_degree : ∀ i, i ≠ root → i.val < L → T.degree (q i).val = 2

private theorem adj_iff_of_degree_one [Fintype V] [DecidableRel T.Adj] {u v : V}
    (hdeg : T.degree u = 1) (h : T.Adj u v) (w : V) : T.Adj u w ↔ w = v := by
  obtain ⟨x, hx, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  constructor
  · intro hw
    exact (hunique w hw).trans (hunique v h).symm
  · rintro rfl
    exact h

private theorem adj_or_of_degree_two [Fintype V] [DecidableRel T.Adj] {u v w x : V}
    (hd : T.degree u = 2) (hv : T.Adj u v) (hw : T.Adj u w) (hne : v ≠ w)
    (hx : T.Adj u x) : x = v ∨ x = w := by
  classical
  have hp : ({v, w} : Finset V) ⊆ T.neighborFinset u := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (T.mem_neighborFinset _ _).mpr hv
    · obtain rfl := Finset.mem_singleton.mp hy
      exact (T.mem_neighborFinset _ _).mpr hw
  have heq : ({v, w} : Finset V) = T.neighborFinset u :=
    Finset.eq_of_subset_of_card_le hp (by simp [hne, hd])
  have : x ∈ ({v, w} : Finset V) := heq ▸ (T.mem_neighborFinset _ _).mpr hx
  simpa using this

namespace TerminalArms

variable [Fintype V] [DecidableRel T.Adj] (A : TerminalArms T z L)

theorem leaf (v : V) : T.Adj z v ↔ v = (A.q 0).val :=
  adj_iff_of_degree_one A.tip_degree A.tip_adj v

/-- Any edge from the path to its exterior in the surviving tree leaves at the root. -/
theorem external_adj {i : Fin (L + 1)} {w : Surviving z}
    (hw : w ∉ Set.range A.q) (h : (surviving T z).Adj (A.q i) w) : i = A.root := by
  by_contra hi
  change T.Adj (A.q i).val w.val at h
  have hiL := i.isLt
  have hL := A.shorter
  have hnot (j : Fin (L + 1)) : w.val ≠ (A.q j).val :=
    fun he => hw ⟨j, Subtype.ext he.symm⟩
  by_cases hlast : i.val = L
  · have he : i = Fin.last L := Fin.ext hlast
    let j : Fin (L + 1) := ⟨L - 1, by omega⟩
    have hp := A.step j i (by dsimp [j]; omega)
    have hd : T.degree (A.q i).val = 1 := he ▸ A.long_degree
    exact hnot j ((adj_iff_of_degree_one hd hp.symm w.val).mp h)
  · have hd := A.internal_degree i hi (by omega)
    let j : Fin (L + 1) := ⟨i.val + 1, by omega⟩
    have hj := A.step i j rfl
    by_cases hzero : i.val = 0
    · have he : i = 0 := Fin.ext hzero
      have hz : T.Adj (A.q i).val z := he ▸ A.tip_adj.symm
      exact (adj_or_of_degree_two hd hz hj (A.q j).property.symm h).elim w.property (hnot j)
    · let p : Fin (L + 1) := ⟨i.val - 1, by omega⟩
      have hp := A.step p i (by dsimp [p]; omega)
      have hpj : (A.q p).val ≠ (A.q j).val := by
        intro he
        have hv := congrArg Fin.val (A.q.injective (Subtype.ext he))
        dsimp [p, j] at hv
        omega
      exact (adj_or_of_degree_two hd hp.symm hj hpj h).elim (hnot p) (hnot j)

/-- The consecutive path edges give an injective graph homomorphism. -/
private def pathHom : pathGraph (L + 1) →g surviving T z where
  toFun := A.q
  map_rel' := by
    intro i j h
    rcases pathGraph_adj.mp h with hij | hji
    · exact A.step i j hij
    · exact (A.step j i hji).symm

theorem surviving_tree (A : TerminalArms T z L) (hT : T.IsTree) : (surviving T z).IsTree :=
  surviving_isTree hT (leaf_subsingleton A.leaf) (A.q 0)

theorem graft_tree (hT : T.IsTree) : (graft T z (A.q (Fin.last L)).val).IsTree :=
  graft_isTree hT (leaf_subsingleton A.leaf) (A.q (Fin.last L)).property

end TerminalArms

private theorem tree_dist_of_path {G : SimpleGraph V} (hG : G.IsTree) {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : G.dist u v = p.length := by
  obtain ⟨q, hq, hlen⟩ := hG.connected.exists_path_of_dist u v
  obtain ⟨_, _, huniq⟩ := hG.existsUnique_path u v
  rw [(huniq p hp).trans (huniq q hq).symm, hlen]

/-- An injective homomorphism from a path into a tree preserves path distances. -/
theorem tree_dist_of_pathHom {U : Type*} {G : SimpleGraph U} {n : ℕ}
    (hG : G.IsTree) (f : pathGraph n →g G) (hf : Function.Injective f) (i j : Fin n) :
    G.dist (f i) (f j) = max i.val j.val - min i.val j.val := by
  have hc := connected_pathGraph.mpr (by have := i.isLt; omega : n ≠ 0)
  obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist i j
  rw [tree_dist_of_path hG (hp.map hf), Walk.length_map, hlen,
    OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, Nat.dist_eq_max_sub_min]

namespace TerminalArms

variable [Fintype V] [DecidableRel T.Adj] (A : TerminalArms T z L)

theorem path_dist (hT : T.IsTree) (i j : Fin (L + 1)) :
    (surviving T z).dist (A.q i) (A.q j) = max i.val j.val - min i.val j.val :=
  tree_dist_of_pathHom (A.surviving_tree hT) A.pathHom A.q.injective i j

private theorem root_mem_support {u v : Surviving z} (p : (surviving T z).Walk u v)
    (hu : u ∉ Set.range A.q) (hv : v ∈ Set.range A.q) : A.q A.root ∈ p.support := by
  induction p with
  | nil => exact (hu hv).elim
  | @cons u w v hadj p ih =>
      rw [Walk.support_cons]
      apply List.mem_cons_of_mem
      by_cases hw : w ∈ Set.range A.q
      · obtain ⟨i, rfl⟩ := hw
        rw [← A.external_adj hu hadj.symm]
        exact p.start_mem_support
      · exact ih hw hv

/-- The only entrance from outside the two arms is the common root. -/
theorem external_dist (hT : T.IsTree) {w : Surviving z} (hw : w ∉ Set.range A.q)
    (i : Fin (L + 1)) :
    (surviving T z).dist w (A.q i) =
      (surviving T z).dist w (A.q A.root) +
        (max A.root.val i.val - min A.root.val i.val) := by
  have hc := (A.surviving_tree hT).connected
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist w (A.q i)
  classical
  have hmem := A.root_mem_support p hw ⟨i, rfl⟩
  have ht := length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hmem)
  have hd := length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hmem)
  have hsum := congrArg Walk.length (p.take_spec hmem)
  rw [Walk.length_append, ht, hd, hp, A.path_dist hT] at hsum
  exact hsum.symm

end TerminalArms
end OmegaMath.TreeGraft

end Arms

section PendantPaths

namespace OmegaMath.TreeGraft

variable {V : Type*} {T : SimpleGraph V} {v : V}

/-- A pendant path in Definition 2.6, with its root at index zero. -/
structure PendantArm [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (v : V) (a : ℕ) where
  path : pathGraph (a + 1) →g T
  injective : Function.Injective path
  root : path 0 = v
  tip_degree : T.degree (path (Fin.last a)) = 1
  internal_degree : ∀ i : Fin (a + 1), 0 < i.val → i.val < a → T.degree (path i) = 2

private theorem same_first_of_dist (hT : T.IsTree) {x y u : V}
    (hx : T.Adj v x) (hy : T.Adj v y)
    (hdx : T.dist v u = 1 + T.dist x u) (hdy : T.dist v u = 1 + T.dist y u) : x = y := by
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist x u
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist y u
  have hp' : (p.cons hx).length = T.dist v u := by rw [Walk.length_cons, hp, hdx, Nat.add_comm]
  have hq' : (q.cons hy).length = T.dist v u := by rw [Walk.length_cons, hq, hdy, Nat.add_comm]
  obtain ⟨_, _, huniq⟩ := hT.existsUnique_path v u
  have he := (huniq _ ((p.cons hx).isPath_of_length_eq_dist hp')).trans
    (huniq _ ((q.cons hy).isPath_of_length_eq_dist hq')).symm
  simpa using congrArg (fun w : T.Walk v u => w.getVert 1) he

namespace PendantArm

variable [Fintype V] [DecidableRel T.Adj] {a b : ℕ}
variable (X : PendantArm T v a) (Y : PendantArm T v b)

def first (ha : 1 ≤ a) : V := X.path ⟨1, by omega⟩

private theorem dist_from_root (hT : T.IsTree) (i : Fin (a + 1)) : T.dist v (X.path i) = i.val := by
  calc
    T.dist v (X.path i) = T.dist (X.path 0) (X.path i) :=
      congrArg (fun w => T.dist w (X.path i)) X.root.symm
    _ = i.val := by rw [tree_dist_of_pathHom hT X.path X.injective]; simp

/-- Distinct first edges of two paths in a tree force disjointness away from the root. -/
private theorem shared_only_root (hT : T.IsTree) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hfirst : X.first ha ≠ Y.first hb) {i : Fin (a + 1)} {j : Fin (b + 1)}
    (he : X.path i = Y.path j) : i.val = 0 ∧ j.val = 0 := by
  have hij : i.val = j.val := by
    rw [← X.dist_from_root hT i, he, Y.dist_from_root hT j]
  by_cases hi : i.val = 0
  · exact ⟨hi, hij.symm.trans hi⟩
  · exfalso
    apply hfirst
    have hfirst_adj {m : ℕ} (P : PendantArm T v m) (hm : 1 ≤ m) :
        T.Adj v (P.first hm) := by
      have hs : (pathGraph (m + 1)).Adj 0 ⟨1, by omega⟩ :=
        pathGraph_adj.mpr (Or.inl rfl)
      have hd := P.path.map_rel hs
      change T.Adj (P.path 0) (P.first hm) at hd
      simpa only [P.root] using hd
    have hdist {m : ℕ} (P : PendantArm T v m) (hm : 1 ≤ m) (p : Fin (m + 1))
        (hp : 0 < p.val) : T.dist v (P.path p) = 1 + T.dist (P.first hm) (P.path p) := by
      rw [P.dist_from_root hT p]
      change p.val = 1 + T.dist (P.path ⟨1, _⟩) (P.path p)
      rw [tree_dist_of_pathHom hT P.path P.injective]
      change p.val = 1 + (max 1 p.val - min 1 p.val)
      have hp' : 1 ≤ p.val := hp
      rw [max_eq_right hp', min_eq_left hp']
      omega
    exact same_first_of_dist hT (hfirst_adj X ha) (hfirst_adj Y hb) (hdist X ha i (by omega))
      (he ▸ hdist Y hb j (by omega))

private def joinedVertex (hb : 1 ≤ b) (i : Fin (a + b - 1 + 1)) : V :=
  if hi : i.val ≤ b - 1 then Y.path ⟨b - 1 - i.val, by omega⟩
  else X.path ⟨i.val - (b - 1), by have := i.isLt; omega⟩

private theorem joined_left (hb : 1 ≤ b) (i : Fin (a + b - 1 + 1))
    (hi : i.val ≤ b - 1) :
    X.joinedVertex Y hb i = Y.path ⟨b - 1 - i.val, by omega⟩ := dite_eq_left hi

private theorem joined_right (hb : 1 ≤ b) (i : Fin (a + b - 1 + 1))
    (hi : b - 1 ≤ i.val) :
    X.joinedVertex Y hb i = X.path ⟨i.val - (b - 1), by have := i.isLt; omega⟩ := by
  by_cases hi' : i.val ≤ b - 1
  · rw [X.joined_left Y hb i hi']
    have h₁ : (⟨b - 1 - i.val, by omega⟩ : Fin (b + 1)) = 0 := Fin.ext (by simp; omega)
    have h₂ : (⟨i.val - (b - 1), by have := i.isLt; omega⟩ : Fin (a + 1)) = 0 :=
      Fin.ext (by change i.val - (b - 1) = 0; omega)
    rw [h₁, h₂, X.root, Y.root]
  · exact dite_eq_right hi'

private theorem joined_injective (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) :
    Function.Injective (X.joinedVertex Y hb) := by
  intro i j he
  have hleft (i j : Fin (a + b - 1 + 1)) (hi : i.val ≤ b - 1) (hj : j.val ≤ b - 1)
      (he : X.joinedVertex Y hb i = X.joinedVertex Y hb j) : i = j := by
    rw [X.joined_left Y hb i hi, X.joined_left Y hb j hj] at he
    have hval := congrArg Fin.val (Y.injective he)
    change b - 1 - i.val = b - 1 - j.val at hval
    apply Fin.ext
    omega
  have hright (i j : Fin (a + b - 1 + 1)) (hi : b - 1 ≤ i.val) (hj : b - 1 ≤ j.val)
      (he : X.joinedVertex Y hb i = X.joinedVertex Y hb j) : i = j := by
    rw [X.joined_right Y hb i hi, X.joined_right Y hb j hj] at he
    have hval := congrArg Fin.val (X.injective he)
    change i.val - (b - 1) = j.val - (b - 1) at hval
    apply Fin.ext
    omega
  have hcross (i j : Fin (a + b - 1 + 1)) (hi : i.val ≤ b - 1) (hj : ¬ j.val ≤ b - 1)
      (he : X.joinedVertex Y hb i = X.joinedVertex Y hb j) : False := by
    rw [X.joined_left Y hb i hi, X.joined_right Y hb j (by omega)] at he
    have h := X.shared_only_root Y hT (hb.trans hab) hb hfirst he.symm
    change j.val - (b - 1) = 0 ∧ _ at h
    omega
  by_cases hi : i.val ≤ b - 1 <;> by_cases hj : j.val ≤ b - 1
  · exact hleft i j hi hj he
  · exact (hcross i j hi hj he).elim
  · exact (hcross j i hj hi he.symm).elim
  · exact hright i j (by omega) (by omega) he

private theorem joined_not_tip (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) (i : Fin (a + b - 1 + 1)) :
    X.joinedVertex Y hb i ≠ Y.path (Fin.last b) := by
  intro he
  by_cases hi : i.val ≤ b - 1
  · rw [X.joined_left Y hb i hi] at he
    have := congrArg Fin.val (Y.injective he)
    simp only [Fin.val_last] at this
    omega
  · rw [X.joined_right Y hb i (by omega)] at he
    have h := X.shared_only_root Y hT (hb.trans hab) hb hfirst he
    simp only [Fin.val_last] at h
    omega

private theorem joined_step (hb : 1 ≤ b) (i j : Fin (a + b - 1 + 1))
    (hij : i.val + 1 = j.val) : T.Adj (X.joinedVertex Y hb i) (X.joinedVertex Y hb j) := by
  by_cases hj : j.val ≤ b - 1
  · rw [X.joined_left Y hb i (by omega), X.joined_left Y hb j hj]
    apply Y.path.map_rel
    exact pathGraph_adj.mpr (Or.inr (by change b - 1 - j.val + 1 = b - 1 - i.val; omega))
  · rw [X.joined_right Y hb i (by omega), X.joined_right Y hb j (by omega)]
    apply X.path.map_rel
    exact pathGraph_adj.mpr (Or.inl (by change i.val - (b - 1) + 1 = j.val - (b - 1); omega))

/-- Reverse the shorter arm up to the common root and continue along the longer arm.
The moved tip is removed from the index set. -/
def terminalArms (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) :
    TerminalArms T (Y.path (Fin.last b)) (a + b - 1) where
  q := ⟨fun i => ⟨X.joinedVertex Y hb i, X.joined_not_tip Y hT hb hab hfirst i⟩,
    fun _ _ he => X.joined_injective Y hT hb hab hfirst (congrArg Subtype.val he)⟩
  root := ⟨b - 1, by omega⟩
  shorter := by change 2 * (b - 1) < a + b - 1; omega
  step := X.joined_step Y hb
  tip_adj := by
    change T.Adj (Y.path (Fin.last b)) (X.joinedVertex Y hb 0)
    rw [X.joined_left Y hb 0 (Nat.zero_le _)]
    apply Y.path.map_rel
    exact pathGraph_adj.mpr (Or.inr (by change b - 1 - 0 + 1 = b; omega))
  tip_degree := Y.tip_degree
  long_degree := by
    change T.degree (X.joinedVertex Y hb (Fin.last (a + b - 1))) = 1
    rw [X.joined_right Y hb _ (by simp; omega)]
    convert X.tip_degree using 3
    apply Fin.ext
    change a + b - 1 - (b - 1) = a
    omega
  internal_degree := by
    intro i hi hiL
    change T.degree (X.joinedVertex Y hb i) = 2
    have hs : i.val ≠ b - 1 := fun he => hi (Fin.ext he)
    by_cases hside : i.val ≤ b - 1
    · rw [X.joined_left Y hb i hside]
      exact Y.internal_degree _ (by change 0 < b - 1 - i.val; omega)
        (by change b - 1 - i.val < b; omega)
    · rw [X.joined_right Y hb i (by omega)]
      exact X.internal_degree _ (by change 0 < i.val - (b - 1); omega)
        (by change i.val - (b - 1) < a; omega)

@[simp] private theorem terminalArms_left (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) :
    ((X.terminalArms Y hT hb hab hfirst).q 0).val = Y.path ⟨b - 1, by omega⟩ := by
  change X.joinedVertex Y hb 0 = _
  rw [X.joined_left Y hb 0 (Nat.zero_le _)]
  rfl

@[simp] theorem terminalArms_right (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) :
    ((X.terminalArms Y hT hb hab hfirst).q (Fin.last (a + b - 1))).val = X.path (Fin.last a) := by
  change X.joinedVertex Y hb (Fin.last (a + b - 1)) = _
  rw [X.joined_right Y hb _ (by simp; omega)]
  congr 1
  apply Fin.ext
  change a + b - 1 - (b - 1) = a
  omega

/-- The terminal-leaf move in Definition 2.7, on the original vertex carrier. -/
def move (hb : 1 ≤ b) : SimpleGraph V :=
  T.deleteEdges {s(Y.path (Fin.last b), Y.path ⟨b - 1, by omega⟩)} ⊔
    SimpleGraph.edge (Y.path (Fin.last b)) (X.path (Fin.last a))

theorem move_eq_graft (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) :
    X.move Y hb = graft T (Y.path (Fin.last b)) (X.path (Fin.last a)) := by
  let A := X.terminalArms Y hT hb hab hfirst
  have h := graft_eq_delete_edge (r := X.path (Fin.last a)) A.leaf
  rw [terminalArms_left] at h
  exact h.symm

end PendantArm
end OmegaMath.TreeGraft

end PendantPaths
