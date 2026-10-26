/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/Geodesics
   mirror-E: none(waiver:no-computational-evidence)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Mandatory shortest-path vertices give rooted distance identities and an inward replacement for visible common-neighbor triples. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Model

/-! Original-host mutual visibility and its finite reconfiguration geometry. -/

set_option autoImplicit false

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

theorem mandatory_dist (hH : H.Connected) {a u v : V}
    (ha : Mandatory H a u v) :
    H.dist u a + H.dist a v = H.dist u v := by
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
  exact shortest_member_dist hp (ha p hp)

theorem mandatory_symm {a u v : V} (ha : Mandatory H a u v) :
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

private theorem mandatory_ancestor (hH : H.Connected) {a b v w : V}
    (ha : Mandatory H a v w) (hb : Mandatory H b v w) (hab : a ≠ b)
    (hh : H.dist a w ≤ H.dist b w) : Mandatory H a b w := by
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist v w
  have hbmem := hb p hp
  have hprefix := length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hbmem)
  have hbd := shortest_member_dist hp hbmem
  have had := mandatory_dist hH ha
  intro q hq
  have hlen : ((p.takeUntil b hbmem).append q).length = H.dist v w := by
    simp only [Walk.length_append, hprefix, hq]
    exact hbd
  have hamem := ha _ hlen
  rcases (Walk.mem_support_append_iff _ _).mp hamem with h | h
  · have hprefa := shortest_member_dist hprefix h
    have habpos := (hH a b).pos_dist_of_ne hab
    omega
  · exact h

private theorem ancestors_comparable (hH : H.Connected) {a b v w : V}
    (ha : Mandatory H a v w) (hb : Mandatory H b v w)
    (haw : a ≠ w) (hbw : b ≠ w) (hab : a ≠ b) :
    Dominates H w a b ∨ Dominates H w b a := by
  rcases le_total (H.dist a w) (H.dist b w) with h | h
  · exact Or.inl ⟨haw, hab, mandatory_ancestor hH ha hb hab h⟩
  · exact Or.inr ⟨hbw, hab.symm, mandatory_ancestor hH hb ha hab.symm h⟩

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
  rcases (Walk.mem_support_append_iff _ _).mp hmem with h | h
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

private theorem triple_visible_of_geodesics {a b c : V}
    (hab : ∃ p : H.Walk a b, p.length = H.dist a b ∧ c ∉ p.support)
    (hac : ∃ p : H.Walk a c, p.length = H.dist a c ∧ b ∉ p.support)
    (hbc : ∃ p : H.Walk b c, p.length = H.dist b c ∧ a ∉ p.support) :
    Visible H {a, b, c} := by
  obtain ⟨p, hp, hcp⟩ := hab
  obtain ⟨q, hq, hbq⟩ := hac
  obtain ⟨r, hr, har⟩ := hbc
  intro u hu v hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (huv rfl).elim
  · refine ⟨p, hp, ?_⟩
    intro z hz hzs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
    rcases hzs with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hcp (h ▸ hz)).elim
  · refine ⟨q, hq, ?_⟩
    intro z hz hzs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
    rcases hzs with h | h | h
    · exact Or.inl h
    · exact (hbq (h ▸ hz)).elim
    · exact Or.inr h
  · refine ⟨p.reverse, by simpa [H.dist_comm] using hp, ?_⟩
    intro z hz hzs
    have hz' : z ∈ p.support := by simpa using hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
    rcases hzs with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact (hcp (h ▸ hz')).elim
  · exact (huv rfl).elim
  · refine ⟨r, hr, ?_⟩
    intro z hz hzs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
    rcases hzs with h | h | h
    · exact (har (h ▸ hz)).elim
    · exact Or.inl h
    · exact Or.inr h
  · refine ⟨q.reverse, by simpa [H.dist_comm] using hq, ?_⟩
    intro z hz hzs
    have hz' : z ∈ q.support := by simpa using hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
    rcases hzs with h | h | h
    · exact Or.inr h
    · exact (hbq (h ▸ hz')).elim
    · exact Or.inl h
  · refine ⟨r.reverse, by simpa [H.dist_comm] using hr, ?_⟩
    intro z hz hzs
    have hz' : z ∈ r.support := by simpa using hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzs
    rcases hzs with h | h | h
    · exact (har (h ▸ hz')).elim
    · exact Or.inr h
    · exact Or.inl h
  · exact (huv rfl).elim

private theorem avoiding_geodesic {a u v : V} (h : ¬ Mandatory H a u v) :
    ∃ p : H.Walk u v, p.length = H.dist u v ∧ a ∉ p.support := by
  obtain ⟨p, hp⟩ := not_forall.mp h
  exact ⟨p, not_imp.mp hp⟩

theorem nonvisible_triple_choice {w u v : V}
    (huw : u ≠ w) (hvw : v ≠ w) (huv : u ≠ v)
    (h : ¬ Visible H {u, v, w}) :
    Mandatory H w u v ∨ Dominates H w u v ∨ Dominates H w v u := by
  classical
  by_contra hn
  have h1 : ¬ Mandatory H w u v := fun hm => hn (Or.inl hm)
  have h2 : ¬ Mandatory H u v w := fun hm => hn (Or.inr (Or.inl ⟨huw, huv, hm⟩))
  have h3 : ¬ Mandatory H v u w := fun hm => hn (Or.inr (Or.inr ⟨hvw, huv.symm, hm⟩))
  exact h (triple_visible_of_geodesics
    (avoiding_geodesic h1) (avoiding_geodesic h3) (avoiding_geodesic h2))

private theorem mandatory_prefix {a b u v : V}
    (ha : Mandatory H a u v) (hb : Mandatory H b u a) : Mandatory H b u v := by
  intro p hp
  have hamem := ha p hp
  have hq := length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hamem)
  exact p.support_takeUntil_subset_support hamem (hb _ hq)

private theorem visible_mandatory_contradiction {S : Finset V} (hS : Visible H S)
    {u v a : V} (hu : u ∈ S) (hv : v ∈ S) (ha : a ∈ S)
    (huv : u ≠ v) (hau : a ≠ u) (hav : a ≠ v) (hm : Mandatory H a u v) : False := by
  obtain ⟨p, hp, hx⟩ := hS u hu v hv huv
  exact (hx a (hm p hp) ha).elim hau hav

private theorem separated_not_dominates (hH : H.Connected) {w a b : V}
    (hsep : Mandatory H w a b) (hdom : Dominates H w a b) : False := by
  have hs := mandatory_dist hH hsep
  have hd := mandatory_dist hH hdom.2.2
  have hp := (hH a w).pos_dist_of_ne hdom.1
  rw [H.dist_comm (u := w) (v := b)] at hs
  rw [H.dist_comm (u := b) (v := a)] at hd
  omega

private theorem comparable_triple_obstruction (hH : H.Connected) {w u v z : V}
    (hS : Visible H {u, v, z}) (hdom : Dominates H w u v)
    (hzw : z ≠ w) (hzu : z ≠ u) (hzv : z ≠ v)
    (hnuz : ¬ Visible H {u, z, w}) (hnvz : ¬ Visible H {v, z, w}) : False := by
  have hvw : v ≠ w := by
    have hh := dominates_height hH hdom
    intro he
    subst v
    simp at hh
  rcases nonvisible_triple_choice hdom.1 hzw hzu.symm hnuz with hus | huz | hzu'
  · rcases nonvisible_triple_choice hvw hzw hzv.symm hnvz with hvs | hvz | hzv'
    · have hum : Mandatory H u v z := mandatory_prefix hvs hdom.2.2
      exact visible_mandatory_contradiction hS (by simp) (by simp) (by simp)
        hzv.symm hdom.2.1 hzu.symm hum
    · have htrans : Dominates H w u z :=
        ⟨hdom.1, hzu.symm, mandatory_trans hdom.2.2 hvz.2.2⟩
      exact separated_not_dominates hH hus htrans
    · rcases ancestors_comparable hH hdom.2.2 hzv'.2.2 hdom.1 hzw hzu.symm with h | h
      · exact separated_not_dominates hH hus h
      · exact separated_not_dominates hH (mandatory_symm hus) h
  · rcases nonvisible_triple_choice hvw hzw hzv.symm hnvz with hvs | hvz | hzv'
    · have hvsd := mandatory_dist hH hvs
      have huv := mandatory_dist hH hdom.2.2
      have huzd := mandatory_dist hH huz.2.2
      have hp := (hH u w).pos_dist_of_ne hdom.1
      have ht := hH.dist_triangle (u := v) (v := u) (w := z)
      rw [H.dist_comm (u := w) (v := z)] at hvsd
      rw [H.dist_comm (u := z) (v := u)] at huzd
      omega
    · exact no_selected_chain hH hS (by simp) (by simp) (by simp) hdom hvz
    · exact no_selected_chain hH hS (by simp) (by simp) (by simp) huz hzv'
  · exact no_selected_chain hH hS (by simp) (by simp) (by simp) hzu' hdom

theorem root_hub (hH : H.Connected) {S : Finset V} {w : V}
    (hS : Visible H S) (hcard : 3 ≤ S.card) (hw : w ∉ S)
    (hn : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Visible H {u, v, w}) :
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Mandatory H w u v := by
  intro u hu v hv huv
  have huw : u ≠ w := fun h => hw (h ▸ hu)
  have hvw : v ≠ w := fun h => hw (h ▸ hv)
  rcases nonvisible_triple_choice huw hvw huv (hn u hu v hv huv) with hs | hd | hd
  · exact hs
  · have hsub : ({u, v} : Finset V) ⊆ S := by simp [Finset.insert_subset_iff, hu, hv]
    have hpaircard : ({u, v} : Finset V).card = 2 := by simp [huv]
    have hlt : ({u, v} : Finset V).card < S.card := by omega
    obtain ⟨z, hz, hzpair⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hzu : z ≠ u := by simpa using fun h => hzpair (Finset.mem_insert.mpr (Or.inl h))
    have hzv : z ≠ v := by simpa using fun h => hzpair (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    have hzw : z ≠ w := fun h => hw (h ▸ hz)
    have hvis : Visible H {u, v, z} := visible_mono (by simp [Finset.insert_subset_iff, hu, hv, hz]) hS
    exact (comparable_triple_obstruction hH hvis hd hzw hzu hzv
      (hn u hu z hz hzu.symm) (hn v hv z hz hzv.symm)).elim
  · have hpaircard : ({u, v} : Finset V).card = 2 := by simp [huv]
    obtain ⟨z, hz, hzpair⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : ({u, v} : Finset V).card < S.card)
    have hzu : z ≠ u := by simpa using fun h => hzpair (Finset.mem_insert.mpr (Or.inl h))
    have hzv : z ≠ v := by simpa using fun h => hzpair (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    have hzw : z ≠ w := fun h => hw (h ▸ hz)
    have hvis : Visible H {v, u, z} := visible_mono (by simp [Finset.insert_subset_iff, hu, hv, hz]) hS
    exact (comparable_triple_obstruction hH hvis hd hzw hzv hzu
      (hn v hv z hz hzv.symm) (hn u hu z hz hzu.symm)).elim

theorem visible_comparability_triangle (hH : H.Connected) {S : Finset V}
    (hS : Visible H S) {w a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : Dominates H w a b ∨ Dominates H w b a)
    (hac : Dominates H w a c ∨ Dominates H w c a)
    (hbc : Dominates H w b c ∨ Dominates H w c b) : False := by
  rcases hab with hab | hba <;> rcases hac with hac | hca <;> rcases hbc with hbc | hcb
  · exact no_selected_chain hH hS ha hb hc hab hbc
  · exact no_selected_chain hH hS ha hc hb hac hcb
  · exact no_selected_chain hH hS hc ha hb hca hab
  · exact no_selected_chain hH hS hc ha hb hca hab
  · exact no_selected_chain hH hS hb ha hc hba hac
  · exact no_selected_chain hH hS hb ha hc hba hac
  · exact no_selected_chain hH hS hb hc ha hbc hca
  · exact no_selected_chain hH hS hc hb ha hcb hba

theorem common_neighbor_height (hH : H.Connected) {w u v y : V}
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
  rw [H.dist_comm (u := v) (v := u)] at hdomd
  have hple : H.dist p y ≤ 2 := by
    have h := H.dist_le (Walk.cons hpu (Walk.cons huy .nil))
    simpa using h
  have hpybound := hH.dist_triangle (u := y) (v := p) (w := w)
  rw [H.dist_comm (u := y) (v := p)] at hpybound
  have hpvle : H.dist p v ≤ 1 + H.dist u v := by
    have h := hH.dist_triangle (u := p) (v := u) (w := v)
    rw [dist_eq_one_iff_adj.mpr hpu] at h
    exact h
  have hpvbound := hH.dist_triangle (u := v) (v := p) (w := w)
  rw [H.dist_comm (u := v) (v := p)] at hpvbound
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
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
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
      have hz' : z ∈ (Walk.cons hpu q).support := by simpa only [Walk.support_reverse, List.mem_reverse] using hz
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
      have hz' : z ∈ (Walk.cons hpu (Walk.cons huy .nil)).support := by simpa only [Walk.support_reverse, List.mem_reverse] using hz
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

theorem inward_replacement (hH : H.Connected) {w u v y p : V}
    (hdom : Dominates H w u v) (huy : H.Adj u y) (hvy : H.Adj v y)
    (hpu : H.Adj p u) (hp : H.dist p w + 1 = H.dist u w)
    (hS : Visible H {u, v, y}) :
    p ≠ v ∧ p ≠ y ∧ ∃ Q P : Configuration H,
      Q.val = {p, v, y} ∧ P.val = {p, y} ∧
      (reconfiguration H).Adj ⟨{u, v, y}, hS⟩ Q ∧
      (reconfiguration H).Adj Q P ∧
      H.dist p w + H.dist y w < H.dist u w + H.dist v w := by
  have hd := inward_distances hH hdom huy hvy hpu hp
  have hpv : p ≠ v := by
    intro he; subst p
    simp only [H.dist_self] at hd
    omega
  have hpy : p ≠ y := by
    intro he; subst p
    simp only [H.dist_self] at hd
    omega
  have hQ : Visible H {p, v, y} := inward_triple_visible hH hdom huy hvy hpu hp hS
  have hP : Visible H {p, y} := visible_pair hH p y
  refine ⟨hpv, hpy, ⟨{p, v, y}, hQ⟩, ⟨{p, y}, hP⟩, rfl, rfl, ?_, ?_, ?_⟩
  · have hs : ({u, v, y} : Finset V) \ {p, v, y} = {u} := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      have := hpu.ne
      have := huy.ne
      have := hdom.2.1
      aesop
    have ht : ({p, v, y} : Finset V) \ {u, v, y} = {p} := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      have := hpu.ne
      aesop
    refine ⟨?_, Or.inr ⟨u, p, hs, ht, hpu.symm⟩⟩
    intro he
    change ({u, v, y} : Finset V) = {p, v, y} at he
    rw [he] at hs
    simp at hs
  · have he : ({p, v, y} : Finset V).erase v = {p, y} := by
      ext z
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      have := hvy.ne
      aesop
    have hm := mixedMove_erase H ({p, v, y} : Finset V) (x := v) (by simp)
    rw [he] at hm
    exact hm
  · have hy := common_neighbor_height hH hdom huy hvy
    have hh := dominates_height hH hdom
    omega

end D5.S3.Combinatorics.Graph.MutualVisibility
