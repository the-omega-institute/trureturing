/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/Geodesics
   mirror-E: none(waiver:no-computational-evidence)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Mandatory shortest-path vertices give rooted distance identities and an inward replacement for visible common-neighbor triples. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Model

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph

variable {V : Type*} [DecidableEq V] {H : SimpleGraph V}

/-- Every shortest original-host path between the endpoints contains the given vertex. -/
def Mandatory (H : SimpleGraph V) (a u v : V) : Prop :=
  ∀ p : H.Walk u v, p.length = H.dist u v → a ∈ p.support

/-- Strict mandatory ancestry towards a root. -/
def Dominates (H : SimpleGraph V) (w u v : V) : Prop :=
  u ≠ w ∧ u ≠ v ∧ Mandatory H u v w

private theorem shortest_member_dist {u v a : V} {p : H.Walk u v}
    (hp : p.length = H.dist u v) (ha : a ∈ p.support) :
    H.dist u a + H.dist a v = H.dist u v := by
  have hq := length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil ha)
  have hr := length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil ha)
  rw [← hq, ← hr, ← Walk.length_append, p.take_spec ha, hp]

private theorem mandatory_dist (hH : H.Connected) {a u v : V}
    (ha : Mandatory H a u v) :
    H.dist u a + H.dist a v = H.dist u v := by
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
  exact shortest_member_dist hp (ha p hp)

private theorem mandatory_symm {a u v : V} (ha : Mandatory H a u v) :
    Mandatory H a v u := by
  intro p hp
  have hr : p.reverse.length = H.dist u v := by
    simpa [H.dist_comm] using hp
  simpa using ha p.reverse hr

private theorem dominates_height (hH : H.Connected) {w u v : V}
    (h : Dominates H w u v) : H.dist u w < H.dist v w := by
  have hm := mandatory_dist hH h.2.2
  have hp := (hH v u).pos_dist_of_ne h.2.1.symm
  omega

private theorem mandatory_trans {a b c w : V}
    (ha : Mandatory H a b w) (hb : Mandatory H b c w) :
    Mandatory H a c w := by
  intro p hp
  have hbmem := hb p hp
  have hq := length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hbmem)
  exact p.support_dropUntil_subset_support hbmem (ha _ hq)

private theorem shortest_height_le {x w z : V} {p : H.Walk x w}
    (hp : p.length = H.dist x w) (hz : z ∈ p.support) :
    H.dist z w ≤ H.dist x w := by
  have hm := shortest_member_dist hp hz
  omega

private theorem mandatory_segment (hH : H.Connected) {w a b c : V}
    (ha : Dominates H w a b) (hb : Dominates H w b c) :
    Mandatory H b c a := by
  have hab := mandatory_dist hH ha.2.2
  have hbc := mandatory_dist hH hb.2.2
  have hac : Mandatory H a c w := mandatory_trans ha.2.2 hb.2.2
  have hacd := mandatory_dist hH hac
  have habHeight := dominates_height hH ha
  intro p hp
  obtain ⟨q, hq⟩ := hH.exists_walk_length_eq_dist a w
  have hlen : (p.append q).length = H.dist c w := by
    simp only [Walk.length_append, hp, hq]
    exact hacd
  have hmem := hb.2.2 (p.append q) hlen
  rcases Walk.mem_support_append_iff.mp hmem with h | h
  · exact h
  · have := shortest_height_le hq h
    omega

private theorem no_selected_chain (hH : H.Connected) {S : Finset V} (hS : Visible H S)
    {w a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : Dominates H w a b) (hbc : Dominates H w b c) : False := by
  have hac : a ≠ c := by
    have h1 := dominates_height hH hab
    have h2 := dominates_height hH hbc
    intro he
    rw [he] at h1
    omega
  obtain ⟨p, hp, havoid⟩ := hS c hc a ha hac.symm
  have hmem := mandatory_segment hH hab hbc p hp
  rcases havoid b hmem hb with h | h
  · exact hbc.2.1 h
  · exact hab.2.1 h.symm

private theorem visible_pair_avoids_third {a b z : V}
    (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
    (hS : Visible H {a, b, z}) :
    ∃ p : H.Walk a b, p.length = H.dist a b ∧ z ∉ p.support := by
  obtain ⟨p, hp, ha⟩ := hS a (by simp) b (by simp) hab
  refine ⟨p, hp, ?_⟩
  intro hz
  rcases ha z hz (by simp) with h | h
  · exact hza h
  · exact hzb h

private theorem common_neighbor_height (hH : H.Connected) {w u v y : V}
    (hdom : Dominates H w u v) (huy : H.Adj u y) (hvy : H.Adj v y) :
    H.dist y w = H.dist u w + 1 := by
  have hlen := mandatory_dist hH hdom.2.2
  have huvpos := (hH v u).pos_dist_of_ne hdom.2.1.symm
  have huvle : H.dist v u ≤ 2 := by
    have h := H.dist_le (Walk.cons hvy (Walk.cons huy.symm .nil))
    simpa using h
  have huylen : H.dist u y = 1 := dist_eq_one_iff_adj.mpr huy
  have hvylen : H.dist v y = 1 := dist_eq_one_iff_adj.mpr hvy
  have hyulen : H.dist y u = 1 := dist_eq_one_iff_adj.mpr huy.symm
  have hyvlen : H.dist y v = 1 := dist_eq_one_iff_adj.mpr hvy.symm
  have h1 : H.dist y w ≤ H.dist u w + 1 := by
    have := hH.dist_triangle (u := y) (v := u) (w := w)
    omega
  have h2 := hH.dist_triangle (u := v) (v := y) (w := w)
  by_contra hne
  have hdist : H.dist y w = H.dist u w := by omega
  obtain ⟨q, hq⟩ := hH.exists_walk_length_eq_dist y w
  have huavoid : u ∉ q.support := by
    intro hu
    have hm := shortest_member_dist hq hu
    omega
  have hpath : (Walk.cons hvy q).length = H.dist v w := by
    simp only [Walk.length_cons, hq]
    omega
  have hu := hdom.2.2 (Walk.cons hvy q) hpath
  simp only [Walk.support_cons, List.mem_cons] at hu
  exact hu.elim hdom.2.1 huavoid

private theorem inward_distances (hH : H.Connected) {w u v y p : V}
    (hdom : Dominates H w u v) (huy : H.Adj u y) (hvy : H.Adj v y)
    (hpu : H.Adj p u) (hp : H.dist p w + 1 = H.dist u w) :
    H.dist p y = 2 ∧ H.dist p v = H.dist u v + 1 := by
  have hy := common_neighbor_height hH hdom huy hvy
  have hdomd := mandatory_dist hH hdom.2.2
  rw [H.dist_comm v u] at hdomd
  have hple : H.dist p y ≤ 2 := by
    have h := H.dist_le (Walk.cons hpu (Walk.cons huy .nil))
    simpa using h
  have hpybound := hH.dist_triangle (u := y) (v := p) (w := w)
  rw [H.dist_comm y p] at hpybound
  have hpvle : H.dist p v ≤ 1 + H.dist u v := by
    have h := hH.dist_triangle (u := p) (v := u) (w := v)
    rw [dist_eq_one_iff_adj.mpr hpu] at h
    exact h
  have hpvbound := hH.dist_triangle (u := v) (v := p) (w := w)
  rw [H.dist_comm v p] at hpvbound
  constructor <;> omega

private theorem inward_triple_visible (hH : H.Connected) {w u v y p : V}
    (hdom : Dominates H w u v) (huy : H.Adj u y) (hvy : H.Adj v y)
    (hpu : H.Adj p u) (hp : H.dist p w + 1 = H.dist u w)
    (hS : Visible H {u, v, y}) : Visible H {p, v, y} := by
  have hdist := inward_distances hH hdom huy hvy hpu hp
  have hpv : p ≠ v := by
    intro he; subst p
    simp only [H.dist_self] at hdist
    omega
  have hpy : p ≠ y := by
    intro he; subst p
    simp only [H.dist_self] at hdist
    omega
  obtain ⟨q, hq, hyq⟩ := visible_pair_avoids_third hdom.2.1
    huy.ne.symm hvy.ne.symm hS
  have hq' : (Walk.cons hpu q).length = H.dist p v := by
    simp only [Walk.length_cons, hq]
    omega
  have hyq' : y ∉ (Walk.cons hpu q).support := by
    simpa using (show y ≠ p ∧ y ∉ q.support from ⟨hpy.symm, hyq⟩)
  have hpypath : (Walk.cons hpu (Walk.cons huy .nil)).length = H.dist p y := by
    simpa using hdist.1.symm
  have hvpypath : v ∉ (Walk.cons hpu (Walk.cons huy .nil)).support := by
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton]
    exact fun h => h.elim hpv.symm (fun h => h.elim hdom.2.1.symm hvy.ne)
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (hab rfl).elim
  · exact ⟨_, hq', fun z hz hzs => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
      rcases hzs with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · subst z; exact (hyq' hz).elim⟩
  · exact ⟨_, hpypath, fun z hz hzs => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
      rcases hzs with h | h | h
      · exact Or.inl h
      · subst z; exact (hvpypath hz).elim
      · exact Or.inr h⟩
  · refine ⟨(Walk.cons hpu q).reverse, ?_, ?_⟩
    · simpa [H.dist_comm] using hq'
    · intro z hz hzs
      have hz' : z ∈ (Walk.cons hpu q).support := by simpa using hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
      rcases hzs with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · subst z; exact (hyq' hz').elim
  · exact (hab rfl).elim
  · refine ⟨hvy.toWalk, ?_, ?_⟩
    · simpa using (dist_eq_one_iff_adj.mpr hvy).symm
    · intro z hz _
      simpa using hz
  · refine ⟨(Walk.cons hpu (Walk.cons huy .nil)).reverse, ?_, ?_⟩
    · simpa [H.dist_comm] using hpypath
    · intro z hz hzs
      have hz' : z ∈ (Walk.cons hpu (Walk.cons huy .nil)).support := by simpa using hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
      rcases hzs with h | h | h
      · exact Or.inr h
      · subst z; exact (hvpypath hz').elim
      · exact Or.inl h
  · refine ⟨hvy.symm.toWalk, ?_, ?_⟩
    · simpa using (dist_eq_one_iff_adj.mpr hvy.symm).symm
    · intro z hz _
      simpa using hz
  · exact (hab rfl).elim

end D5.S3.Combinatorics.Graph.MutualVisibility
