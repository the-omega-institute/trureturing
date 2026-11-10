/- GID: D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BipartiteExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual deletion-witness shapes for bipartite exchange selections. -/

import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import D5.S3.Combinatorics.Graph.StarForming.CubicPathAccounting
import D5.S3.Combinatorics.Graph.StarForming.BipartiteBounds

/-! The received augmented-isolate proof constructs two actual dissociation
selections. Witness choices below come from canonical inclusion-minimality;
no exchange size or graph-parameter inequality is assumed as a premise. -/

namespace D5.S3.Combinatorics.Graph.StarForming.BipartiteExchange
open StarFormingDissociationRefutation Regular
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)

def Isolate (v : V) : Prop := v ∈ S ∧ ∀ w ∈ S, ¬ G.Adj v w

def LeafAt (u h : V) : Prop := u ∈ S ∧ High G.Adj (· ∈ S) h ∧
  G.Adj u h ∧ ∀ w ∈ S, G.Adj u w → w = h

/-- A selected high vertex has an actual outside deletion witness. -/
noncomputable def witness (hS : IsMinimalStarForming G 2 S) (v : V) : V := by
  classical
  exact if hv : High G.Adj (· ∈ S) v then
    Classical.choose (high_has_failure G.Adj (· ∈ S) (fun _ => G.irrefl)
      ((regular_minimal_iff G S).mpr hS) v hv)
  else v

/-- The chosen map retains the original failure predicate. -/
theorem witness_failure (hS : IsMinimalStarForming G 2 S) (v : V)
    (hv : High G.Adj (· ∈ S) v) : Failure G.Adj (· ∈ S) v (witness G S hS v) := by
  classical
  unfold witness
  rw [dif_pos hv]
  exact Classical.choose_spec (high_has_failure G.Adj (· ∈ S) (fun _ => G.irrefl)
    ((regular_minimal_iff G S).mpr hS) v hv)

/-- Different high vertices have different chosen witnesses. -/
theorem witness_injective (hS : IsMinimalStarForming G 2 S) (v w : V)
    (hv : High G.Adj (· ∈ S) v) (hw : High G.Adj (· ∈ S) w)
    (he : witness G S hS v = witness G S hS w) : v = w := by
  apply failure_witnesses_disjoint G.Adj (· ∈ S)
    ((regular_minimal_iff G S).mpr hS).1 v w (witness G S hS v) hv hw
    (witness_failure G S hS v hv)
  rw [he]
  exact witness_failure G S hS w hw

/-- In a two-colorable graph an adjacent high witness can meet no other
selected nonisolate. This is the exact source local theorem, with its graph
hypotheses discharged by the actual coloring. -/
theorem adjacent_other_isolate (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (h x y : V)
    (hf : Failure G.Adj (· ∈ S) h x) (hxh : G.Adj x h)
    (hy : y ∈ S) (hne : y ≠ h) (hxy : G.Adj x y) : Isolate G S y := by
  refine ⟨hy,?_⟩
  apply CubicStability.high_adjacent_failure_other_neighbor_is_isolated G.Adj (· ∈ S)
    (fun _ _ hh => G.adj_symm hh) ?_ h x y hf hxh hxy hy hne
  intro a b c hab hac hbc
  have hab' := hcolor a b hab
  have hac' := hcolor a c hac
  have hbc' := hcolor b c hbc
  cases ha : color a <;> cases hb : color b <;> cases hc : color c <;> simp_all

/-- A nonadjacent high failure has one selected neighbor, which is a leaf
whose unique selected support is the deleted high vertex. -/
theorem nonadjacent_leaf (hS : IsMinimalStarForming G 2 S) (h x : V)
    (hh : High G.Adj (· ∈ S) h) (hf : Failure G.Adj (· ∈ S) h x)
    (hne : ¬ G.Adj x h) :
    ∃ u, LeafAt G S u h ∧ G.Adj x u ∧ ∀ w ∈ S, G.Adj x w → w = u := by
  have hm := (regular_minimal_iff G S).mpr hS
  have hu : ∃ u, u ∈ S ∧ G.Adj x u := by
    rcases hm.1 x hf.1 with ha | hb
    · obtain ⟨a,b,ha,hb,hab,hxa,hxb⟩ := ha
      exact ⟨a,ha,hxa⟩
    · obtain ⟨u,v,hu,hv,hxu,huv⟩ := hb
      exact ⟨u,hu,hxu⟩
  obtain ⟨u,hu,hxu⟩ := hu
  have hxu_unique : ∀ w ∈ S, G.Adj x w → w = u := by
    intro w hw hxw
    exact nonadjacent_witness_unique_neighbor G.Adj (· ∈ S) h x w u hf hne
      hw hu hxw hxu
  have hune : u ≠ h := fun he => hne (he ▸ hxu)
  have hleaf : ∀ w ∈ S, G.Adj u w → w = h := by
    intro w hw huw
    by_contra hwh
    exact hf.2 (Or.inr ⟨u,w,⟨hu,hune⟩,⟨hw,hwh⟩,hxu,huw⟩)
  have huh : G.Adj u h := by
    rcases hm.1 x hf.1 with ha | hb
    · obtain ⟨a,b,ha,hb,hab,hxa,hxb⟩ := ha
      exact (hab ((hxu_unique a ha hxa).trans (hxu_unique b hb hxb).symm)).elim
    · obtain ⟨c,l,hc,hl,hxc,hcl⟩ := hb
      have hcu := hxu_unique c hc hxc
      subst c
      have hlh := hleaf l hl hcl
      exact hlh ▸ hcl
  exact ⟨u,⟨hu,hh,huh,hleaf⟩,hxu,hxu_unique⟩

/-- Leaf support is unique and distinct leaves at one high cannot coincide. -/
theorem leaf_support_unique (u h k : V) (hh : LeafAt G S u h) (hk : LeafAt G S u k) :
    h = k := (hh.2.2.2 k hk.2.1.1 hk.2.2.1).symm

/-- A nonhigh selected vertex has at most one selected neighbor. -/
theorem nonhigh_unique (v x y : V) (hv : v ∈ S)
    (hn : ¬ High G.Adj (· ∈ S) v) (hx : x ∈ S) (hy : y ∈ S)
    (hax : G.Adj v x) (hay : G.Adj v y) : x = y := by
  by_contra hne
  exact hn ⟨hv,x,y,hx,hy,hne,hax,hay⟩

/-- Every chosen good witness reserves its unique selected leaf. -/
def Reserved (hS : IsMinimalStarForming G 2 S) (u : V) : Prop :=
  ∃ h, High G.Adj (· ∈ S) h ∧ ¬ G.Adj (witness G S hS h) h ∧
    G.Adj (witness G S hS h) u ∧ u ∈ S

/-- The unreserved leaves are exactly the additional active owners. -/
def Extra (hS : IsMinimalStarForming G 2 S) (u : V) : Prop :=
  (∃ h, LeafAt G S u h) ∧ ¬ Reserved G S hS u

/-- High vertices and extra leaves receive outside witnesses. -/
def Active (hS : IsMinimalStarForming G 2 S) (u : V) : Prop :=
  High G.Adj (· ∈ S) u ∨ Extra G S hS u

/-- All other nonisolated selected vertices survive both exchanges. -/
def Passive (hS : IsMinimalStarForming G 2 S) (u : V) : Prop :=
  u ∈ S ∧ ¬ Isolate G S u ∧ ¬ Active G S hS u

theorem leaf_not_high (u h : V) (hu : LeafAt G S u h) :
    ¬ High G.Adj (· ∈ S) u := by
  rintro ⟨_,a,b,ha,hb,hab,hua,hub⟩
  exact hab ((hu.2.2.2 a ha hua).trans (hu.2.2.2 b hb hub).symm)

theorem reserved_leaf (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Reserved G S hS u) : ∃ h, LeafAt G S u h ∧
      ¬ G.Adj (witness G S hS h) h ∧ G.Adj (witness G S hS h) u := by
  obtain ⟨h,hh,hn,ha,hus⟩ := hu
  obtain ⟨v,hv,hxv,hunique⟩ := nonadjacent_leaf G S hS h (witness G S hS h)
    hh (witness_failure G S hS h hh) hn
  have he := hunique u hus ha
  subst u
  exact ⟨h,hv,hn,hxv⟩

theorem extra_has_failure (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Extra G S hS u) : ∃ x, Failure G.Adj (· ∈ S) u x ∧ G.Adj x u := by
  obtain ⟨h,hh⟩ := hu.1
  exact CubicStability.leaf_has_adjacent_failure G.Adj (· ∈ S)
    (fun _ => G.irrefl) (fun _ _ hh => G.adj_symm hh)
    ((regular_minimal_iff G S).mpr hS) u h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2

noncomputable def activeWitness (hS : IsMinimalStarForming G 2 S) (u : V) : V := by
  classical
  exact if hh : High G.Adj (· ∈ S) u then witness G S hS u
  else if he : Extra G S hS u then Classical.choose (extra_has_failure G S hS u he)
  else u

theorem active_failure (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Active G S hS u) : Failure G.Adj (· ∈ S) u (activeWitness G S hS u) := by
  classical
  unfold activeWitness
  split_ifs with hh he
  · exact witness_failure G S hS u hh
  · exact (Classical.choose_spec (extra_has_failure G S hS u he)).1
  · exact (he (hu.resolve_left hh)).elim

theorem active_selected (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Active G S hS u) : u ∈ S := by
  rcases hu with hu | hu
  · exact hu.1
  · obtain ⟨h,hh⟩ := hu.1
    exact hh.1

theorem active_not_isolate (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Active G S hS u) : ¬ Isolate G S u := by
  intro hi
  rcases hu with hu | hu
  · obtain ⟨a,b,ha,hb,hab,hua,hub⟩ := hu.2
    exact hi.2 a ha hua
  · obtain ⟨h,hh⟩ := hu.1
    exact hi.2 h hh.2.1.1 hh.2.2.1

theorem extra_witness_adjacent (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Extra G S hS u) : G.Adj (activeWitness G S hS u) u := by
  classical
  obtain ⟨h,hh⟩ := hu.1
  have hn := leaf_not_high G S u h hh
  simp only [activeWitness,dif_neg hn,dif_pos hu]
  exact (Classical.choose_spec (extra_has_failure G S hS u hu)).2

theorem reserved_passive (hS : IsMinimalStarForming G 2 S) (u : V)
    (hu : Reserved G S hS u) : Passive G S hS u := by
  obtain ⟨h,hh,hn,ha⟩ := reserved_leaf G S hS u hu
  refine ⟨hh.1,?_,?_⟩
  · intro hi
    exact hi.2 h hh.2.1.1 hh.2.2.1
  · rintro (hh' | he)
    · exact leaf_not_high G S u h hh hh'
    · exact he.2 hu

/-- Every selected nonisolate met by an active witness is either its owner,
or the unique passive leaf at that owner. -/
theorem active_shape (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (a v : V)
    (ha : Active G S hS a) (hv : v ∈ S)
    (hxv : G.Adj (activeWitness G S hS a) v) :
    Isolate G S v ∨ v = a ∨ (Passive G S hS v ∧ G.Adj a v) := by
  classical
  rcases ha with hh | he
  · have heq : activeWitness G S hS a = witness G S hS a := by
      simp only [activeWitness,dif_pos hh]
    rw [heq] at hxv
    have hf := witness_failure G S hS a hh
    by_cases hxa : G.Adj (witness G S hS a) a
    · by_cases hva : v = a
      · exact Or.inr (Or.inl hva)
      · exact Or.inl (adjacent_other_isolate G S color hcolor a
          (witness G S hS a) v hf hxa hv hva hxv)
    · obtain ⟨u,hu,hxu,hunique⟩ := nonadjacent_leaf G S hS a
        (witness G S hS a) hh hf hxa
      have hvu := hunique v hv hxv
      subst v
      have hr : Reserved G S hS u := ⟨a,hh,hxa,hxu,hu.1⟩
      exact Or.inr (Or.inr ⟨reserved_passive G S hS u hr,G.adj_symm hu.2.2.1⟩)
  · by_cases hva : v = a
    · exact Or.inr (Or.inl hva)
    · obtain ⟨h,hh⟩ := he.1
      exact Or.inl ⟨hv,CubicStability.leaf_failure_other_neighbor_is_isolated
        G.Adj (· ∈ S) (fun _ _ hh => G.adj_symm hh)
        a h (activeWitness G S hS a) v hh.2.1 hh.2.2.2
        (active_failure G S hS a (Or.inr he)) hv hva hxv⟩

/-- The entire active witness image is counted without reuse, including the
extra-leaf additions. -/
theorem activeWitness_injective (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (a b : V)
    (ha : Active G S hS a) (hb : Active G S hS b)
    (heq : activeWitness G S hS a = activeWitness G S hS b) : a = b := by
  classical
  have hleft (v w : V) (hv : Extra G S hS v) (hw : Active G S hS w)
      (he : activeWitness G S hS v = activeWitness G S hS w) : v = w := by
    have hadj := extra_witness_adjacent G S hS v hv
    rw [he] at hadj
    rcases active_shape G S color hcolor hS w v hw
      (active_selected G S hS v (Or.inr hv)) hadj with hi | he | hp
    · exact (active_not_isolate G S hS v (Or.inr hv) hi).elim
    · exact he
    · exact (hp.1.2.2 (Or.inr hv)).elim
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · apply witness_injective G S hS a b ha hb
      simpa only [activeWitness,dif_pos ha,dif_pos hb] using heq
    · exact (hleft b a hb (Or.inl ha) heq.symm).symm
  · exact hleft a b ha hb heq

/-- Active and passive selected edges are preserved when replacing the active
endpoint by its assigned outside witness. -/
theorem active_passive_edges (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (a b : V)
    (ha : Active G S hS a) (hb : Passive G S hS b) :
    G.Adj a b ↔ G.Adj (activeWitness G S hS a) b := by
  classical
  constructor
  · intro hab
    have han : High G.Adj (· ∈ S) a := by
      rcases ha with ha | he
      · exact ha
      · obtain ⟨h,hh⟩ := he.1
        have hbh := hh.2.2.2 b hb.1 hab
        exact (hb.2.2 (Or.inl (hbh ▸ hh.2.1))).elim
    have hbn : ¬ High G.Adj (· ∈ S) b := fun hh => hb.2.2 (Or.inl hh)
    have hleaf : LeafAt G S b a := ⟨hb.1,han,G.adj_symm hab,
      fun v hv hbv => nonhigh_unique G S b v a hb.1 hbn hv han.1 hbv (G.adj_symm hab)⟩
    have hr : Reserved G S hS b := by
      by_contra hn
      exact hb.2.2 (Or.inr ⟨⟨a,hleaf⟩,hn⟩)
    obtain ⟨h,hh,hn,hx⟩ := reserved_leaf G S hS b hr
    have he := leaf_support_unique G S b a h hleaf hh
    subst h
    simpa only [activeWitness,dif_pos han] using hx
  · intro hxb
    rcases active_shape G S color hcolor hS a b ha hb.1 hxb with hi | he | hp
    · exact (hb.2.1 hi).elim
    · exact (hb.2.2 (he ▸ ha)).elim
    · exact hp.2

/-- At most one passive vertex can be adjacent to an active owner. -/
theorem active_passive_unique (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (a b c : V)
    (ha : Active G S hS a) (hb : Passive G S hS b) (hc : Passive G S hS c)
    (hab : G.Adj a b) (hac : G.Adj a c) : b = c := by
  have hxb := (active_passive_edges G S color hcolor hS a b ha hb).mp hab
  have hxc := (active_passive_edges G S color hcolor hS a c ha hc).mp hac
  have hn : ¬ G.Adj (activeWitness G S hS a) a := by
    intro hxa
    have h1 := hcolor _ _ hxa
    have h2 := hcolor _ _ hxb
    have h3 := hcolor _ _ hab
    cases hca : color a <;> cases hcb : color b <;>
      cases hcx : color (activeWitness G S hS a) <;> simp_all
  exact nonadjacent_witness_unique_neighbor G.Adj (· ∈ S) a
    (activeWitness G S hS a) b c (active_failure G S hS a ha) hn hb.1 hc.1 hxb hxc

/-- Both explicit augmented exchanges, indexed by the retained active color. -/
noncomputable def exchange (hS : IsMinimalStarForming G 2 S) (color : V → Bool)
    (c : Bool) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Passive G S hS v ∨
    (Active G S hS v ∧ color v = c) ∨
    (Isolate G S v ∧ color v ≠ c) ∨
    ∃ a, Active G S hS a ∧ activeWitness G S hS a = v ∧ color v ≠ c

private theorem mem_exchange (hS : IsMinimalStarForming G 2 S)
    (color : V → Bool) (c : Bool) (v : V) :
    v ∈ exchange G S hS color c ↔ Passive G S hS v ∨
    (Active G S hS v ∧ color v = c) ∨
    (Isolate G S v ∧ color v ≠ c) ∨
    ∃ a, Active G S hS a ∧ activeWitness G S hS a = v ∧ color v ≠ c := by
  classical
  simp only [exchange,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem common_color (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (v x y : V) (hx : G.Adj v x) (hy : G.Adj v y) : color x = color y := by
  have h1 := hcolor v x hx
  have h2 := hcolor v y hy
  cases hv : color v <;> cases hx : color x <;> cases hy : color y <;> simp_all

private theorem active_neighbor (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) (a v : V)
    (ha : Active G S hS a) (hca : color a = c)
    (hv : v ∈ exchange G S hS color c) (hav : G.Adj a v) :
    Passive G S hS v ∨ v = activeWitness G S hS a := by
  rcases (mem_exchange G S hS color c v).mp hv with hp | ⟨hb,hcb⟩ | ⟨hi,hci⟩ | ⟨b,hb,he,hcv⟩
  · exact Or.inl hp
  · exact (hcolor a v hav (hca.trans hcb.symm)).elim
  · exact (hi.2 a (active_selected G S hS a ha) (G.adj_symm hav)).elim
  · have hxa : G.Adj (activeWitness G S hS b) a := he.symm ▸ G.adj_symm hav
    rcases active_shape G S color hcolor hS b a hb
      (active_selected G S hS a ha) hxa with hi | heq | hp
    · exact (active_not_isolate G S hS a ha hi).elim
    · subst b
      exact Or.inr he.symm
    · exact (hp.1.2.2 ha).elim

private theorem active_exchange_unique (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) (a v w : V)
    (ha : Active G S hS a) (hca : color a = c)
    (hv : v ∈ exchange G S hS color c) (hw : w ∈ exchange G S hS color c)
    (hav : G.Adj a v) (haw : G.Adj a w) : v = w := by
  rcases active_neighbor G S color hcolor hS c a v ha hca hv hav with hpv | hev
  · rcases active_neighbor G S color hcolor hS c a w ha hca hw haw with hpw | hew
    · exact active_passive_unique G S color hcolor hS a v w ha hpv hpw hav haw
    · have hxv := (active_passive_edges G S color hcolor hS a v ha hpv).mp hav
      have heq := common_color G color hcolor v a (activeWitness G S hS a)
        (G.adj_symm hav) (G.adj_symm hxv)
      exact (hcolor a w haw (heq.trans (congrArg color hew).symm)).elim
  · rcases active_neighbor G S color hcolor hS c a w ha hca hw haw with hpw | hew
    · have hxw := (active_passive_edges G S color hcolor hS a w ha hpw).mp haw
      have heq := common_color G color hcolor w a (activeWitness G S hS a)
        (G.adj_symm haw) (G.adj_symm hxw)
      exact (hcolor a v hav (heq.trans (congrArg color hev).symm)).elim
    · exact hev.trans hew.symm

private theorem active_mem_color (hS : IsMinimalStarForming G 2 S)
    (color : V → Bool) (c : Bool) (a : V) (ha : Active G S hS a)
    (he : a ∈ exchange G S hS color c) : color a = c := by
  rcases (mem_exchange G S hS color c a).mp he with hp | ⟨_,hc⟩ | ⟨hi,_⟩ | ⟨b,hb,he,_⟩
  · exact (hp.2.2 ha).elim
  · exact hc
  · exact (active_not_isolate G S hS a ha hi).elim
  · exact ((active_failure G S hS b hb).1 (he.symm ▸ active_selected G S hS a ha)).elim

private theorem passive_neighbor (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) (b v : V)
    (hb : Passive G S hS b) (hv : v ∈ exchange G S hS color c) (hbv : G.Adj b v) :
    v ∈ S ∨ ∃ a, Active G S hS a ∧ v = activeWitness G S hS a ∧
      G.Adj b a ∧ color a ≠ c := by
  rcases (mem_exchange G S hS color c v).mp hv with hp | ⟨ha,_⟩ | ⟨hi,_⟩ | ⟨a,ha,he,hcv⟩
  · exact Or.inl hp.1
  · exact Or.inl (active_selected G S hS v ha)
  · exact Or.inl hi.1
  · have hxb : G.Adj (activeWitness G S hS a) b := he.symm ▸ G.adj_symm hbv
    rcases active_shape G S color hcolor hS a b ha hb.1 hxb with hi | heq | hp
    · exact (hb.2.1 hi).elim
    · exact (hb.2.2 (heq ▸ ha)).elim
    · have hba := G.adj_symm hp.2
      have hc := common_color G color hcolor b a v hba hbv
      exact Or.inr ⟨a,ha,he.symm,hba,fun h => hcv (hc.symm.trans h)⟩

private theorem passive_exchange_unique (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) (b v w : V)
    (hb : Passive G S hS b)
    (hv : v ∈ exchange G S hS color c) (hw : w ∈ exchange G S hS color c)
    (hbv : G.Adj b v) (hbw : G.Adj b w) : v = w := by
  have hn : ¬ High G.Adj (· ∈ S) b := fun h => hb.2.2 (Or.inl h)
  rcases passive_neighbor G S color hcolor hS c b v hb hv hbv with hvs | ⟨a,ha,he,hba,hca⟩
  · rcases passive_neighbor G S color hcolor hS c b w hb hw hbw with hws | ⟨a,ha,he,hba,hca⟩
    · exact nonhigh_unique G S b v w hb.1 hn hvs hws hbv hbw
    · have heq := nonhigh_unique G S b v a hb.1 hn hvs
        (active_selected G S hS a ha) hbv hba
      subst v
      exact (hca (active_mem_color G S hS color c a ha hv)).elim
  · rcases passive_neighbor G S color hcolor hS c b w hb hw hbw with hws | ⟨a',ha',he',hba',hca'⟩
    · have heq := nonhigh_unique G S b w a hb.1 hn hws
        (active_selected G S hS a ha) hbw hba
      subst w
      exact (hca (active_mem_color G S hS color c a ha hw)).elim
    · have heq := nonhigh_unique G S b a a' hb.1 hn
        (active_selected G S hS a ha) (active_selected G S hS a' ha') hba hba'
      exact he.trans ((congrArg (activeWitness G S hS) heq).trans he'.symm)

private theorem outside_neighbor (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) (a v : V)
    (ha : Active G S hS a) (hca : color (activeWitness G S hS a) ≠ c)
    (hv : v ∈ exchange G S hS color c) (hxv : G.Adj (activeWitness G S hS a) v) :
    v = a ∨ (Passive G S hS v ∧ G.Adj a v) := by
  have hvs : v ∈ S := by
    rcases (mem_exchange G S hS color c v).mp hv with hp | ⟨hb,_⟩ | ⟨hi,hci⟩ | ⟨b,hb,he,hcv⟩
    · exact hp.1
    · exact active_selected G S hS v hb
    · exact hi.1
    · have hc : color (activeWitness G S hS a) = color v := by
        cases hx : color (activeWitness G S hS a) <;> cases hv : color v <;>
          cases c <;> simp_all
      exact (hcolor _ _ hxv hc).elim
  rcases active_shape G S color hcolor hS a v ha hvs hxv with hi | he | hp
  · have hcv : color v ≠ c := by
      rcases (mem_exchange G S hS color c v).mp hv with hp | ⟨hb,hcb⟩ | ⟨_,hc⟩ | ⟨b,hb,he,_⟩
      · exact (hp.2.1 hi).elim
      · exact (active_not_isolate G S hS v hb hi).elim
      · exact hc
      · exact ((active_failure G S hS b hb).1 (he.symm ▸ hvs)).elim
    have hc : color (activeWitness G S hS a) = color v := by
      cases hx : color (activeWitness G S hS a) <;> cases hv : color v <;>
        cases c <;> simp_all
    exact (hcolor _ _ hxv hc).elim
  · exact Or.inl he
  · exact Or.inr hp

private theorem outside_exchange_unique (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) (a v w : V)
    (ha : Active G S hS a) (hca : color (activeWitness G S hS a) ≠ c)
    (hv : v ∈ exchange G S hS color c) (hw : w ∈ exchange G S hS color c)
    (hxv : G.Adj (activeWitness G S hS a) v)
    (hxw : G.Adj (activeWitness G S hS a) w) : v = w := by
  rcases outside_neighbor G S color hcolor hS c a v ha hca hv hxv with hev | hpv
  · rcases outside_neighbor G S color hcolor hS c a w ha hca hw hxw with hew | hpw
    · exact hev.trans hew.symm
    · have hc := common_color G color hcolor w a (activeWitness G S hS a)
        (G.adj_symm hpw.2) (G.adj_symm hxw)
      exact (hcolor _ _ hxv (hc.symm.trans (congrArg color hev).symm)).elim
  · rcases outside_neighbor G S color hcolor hS c a w ha hca hw hxw with hew | hpw
    · have hc := common_color G color hcolor v a (activeWitness G S hS a)
        (G.adj_symm hpv.2) (G.adj_symm hxv)
      exact (hcolor _ _ hxw (hc.symm.trans (congrArg color hew).symm)).elim
    · exact active_passive_unique G S color hcolor hS a v w ha hpv.1 hpw.1 hpv.2 hpw.2

/-- Each augmented exchange is an actual canonical dissociation selection. -/
theorem exchange_dissociation (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) (c : Bool) :
    IsKIndependent G 2 (exchange G S hS color c) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff G _).mpr
  intro a ha v hv w hw hav haw
  rcases (mem_exchange G S hS color c a).mp ha with hp | ⟨hb,hcb⟩ | ⟨hi,hci⟩ | ⟨b,hb,he,hca⟩
  · exact passive_exchange_unique G S color hcolor hS c a v w hp hv hw hav haw
  · exact active_exchange_unique G S color hcolor hS c a v w hb hcb hv hw hav haw
  · rcases (mem_exchange G S hS color c v).mp hv with hpv | ⟨hbv,_⟩ | ⟨hiv,_⟩ | ⟨b,hb,he,hcv⟩
    · exact (hi.2 v hpv.1 hav).elim
    · exact (hi.2 v (active_selected G S hS v hbv) hav).elim
    · exact (hi.2 v hiv.1 hav).elim
    · have hc : color a = color v := by
        cases ha : color a <;> cases hv : color v <;> cases c <;> simp_all
      exact (hcolor a v hav hc).elim
  · subst a
    exact outside_exchange_unique G S color hcolor hS c b v w hb hca hv hw hav haw

private noncomputable def activeSet (hS : IsMinimalStarForming G 2 S) : Finset V := by
  classical
  exact S.filter (Active G S hS)
private noncomputable def passiveSet (hS : IsMinimalStarForming G 2 S) : Finset V := by
  classical
  exact S.filter (Passive G S hS)
private noncomputable def isolateSet : Finset V := by
  classical
  exact S.filter (Isolate G S)
private noncomputable def witnessSet (hS : IsMinimalStarForming G 2 S) : Finset V :=
  (activeSet G S hS).image (activeWitness G S hS)

private theorem role_disjoint (hS : IsMinimalStarForming G 2 S) :
    Disjoint (passiveSet G S hS) (activeSet G S hS) ∧
    Disjoint (passiveSet G S hS ∪ activeSet G S hS) (isolateSet G S) ∧
    Disjoint S (witnessSet G S hS) := by
  classical
  refine ⟨?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_filter.mp hv).2.2.2 (Finset.mem_filter.mp hw).2
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    have hi := (Finset.mem_filter.mp hw).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp hv).2.2.1 hi
    · exact active_not_isolate G S hS v (Finset.mem_filter.mp hv).2 hi
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
    exact (active_failure G S hS a (Finset.mem_filter.mp ha).2).1 hv

private theorem roles_partition (hS : IsMinimalStarForming G 2 S) :
    passiveSet G S hS ∪ activeSet G S hS ∪ isolateSet G S = S := by
  classical
  ext v
  simp only [passiveSet,activeSet,isolateSet,Finset.mem_union,Finset.mem_filter]
  constructor
  · rintro ((h | h) | h) <;> exact h.1
  · intro hv
    by_cases hi : Isolate G S v
    · exact Or.inr ⟨hv,hi⟩
    · by_cases ha : Active G S hS v
      · exact Or.inl (Or.inr ⟨hv,ha⟩)
      · exact Or.inl (Or.inl ⟨hv,hv,hi,ha⟩)

private theorem card_exchange (hS : IsMinimalStarForming G 2 S)
    (color : V → Bool) (c : Bool) :
    (exchange G S hS color c).card = (passiveSet G S hS).card +
      ((activeSet G S hS).filter (fun v => color v = c)).card +
      ((isolateSet G S).filter (fun v => color v ≠ c)).card +
      ((witnessSet G S hS).filter (fun v => color v ≠ c)).card := by
  classical
  let P := passiveSet G S hS
  let A := (activeSet G S hS).filter (fun v => color v = c)
  let I := (isolateSet G S).filter (fun v => color v ≠ c)
  let F := (witnessSet G S hS).filter (fun v => color v ≠ c)
  have he : exchange G S hS color c = P ∪ A ∪ I ∪ F := by
    ext v
    simp only [mem_exchange,P,A,I,F,passiveSet,activeSet,isolateSet,witnessSet,
      Finset.mem_union,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro (hp | ⟨ha,hc⟩ | ⟨hi,hc⟩ | ⟨a,ha,he,hc⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨hp.1,hp⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨⟨active_selected G S hS v ha,ha⟩,hc⟩))
      · exact Or.inl (Or.inr ⟨⟨hi.1,hi⟩,hc⟩)
      · exact Or.inr ⟨⟨a,⟨active_selected G S hS a ha,ha⟩,he⟩,hc⟩
    · rintro (((hp | ha) | hi) | hf)
      · exact Or.inl hp.2
      · exact Or.inr (Or.inl ⟨ha.1.2,ha.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hi.1.2,hi.2⟩))
      · obtain ⟨⟨a,ha,he⟩,hc⟩ := hf
        exact Or.inr (Or.inr (Or.inr ⟨a,ha.2,he,hc⟩))
  have hd := role_disjoint G S hS
  have hdPA : Disjoint P A := hd.1.mono_right (Finset.filter_subset _ _)
  have hdPI : Disjoint (P ∪ A) I := hd.2.1.mono
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.filter_subset _ _))
    (Finset.filter_subset _ _)
  have hsub : P ∪ A ∪ I ⊆ S := by
    rw [← roles_partition G S hS]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  have hdF : Disjoint (P ∪ A ∪ I) F := hd.2.2.mono hsub (Finset.filter_subset _ _)
  rw [he,Finset.card_union_of_disjoint hdF,Finset.card_union_of_disjoint hdPI,
    Finset.card_union_of_disjoint hdPA]

private theorem filter_bool_sum (X : Finset V) (color : V → Bool) :
    (X.filter (fun v => color v = false)).card +
      (X.filter (fun v => color v = true)).card = X.card := by
  have he : X.filter (fun v => color v = true) =
      X.filter (fun v => ¬ color v = false) := by
    ext v
    cases color v <;> simp
  rw [he]
  exact Finset.card_filter_add_card_filter_not _

/-- The two actual exchanges count every selected nonisolate twice and each
selected isolate once, after including the injective outside witness image. -/
theorem exchange_card_sum (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hS : IsMinimalStarForming G 2 S) :
    (exchange G S hS color false).card + (exchange G S hS color true).card +
      (DegreeCapacity.isolates G S).card = 2 * S.card := by
  classical
  have hW : (witnessSet G S hS).card = (activeSet G S hS).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb he
    exact activeWitness_injective G S color hcolor hS a b
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he
  have hroles := roles_partition G S hS
  have hd := role_disjoint G S hS
  have hcards : (passiveSet G S hS).card + (activeSet G S hS).card +
      (isolateSet G S).card = S.card := by
    calc
      _ = (passiveSet G S hS ∪ activeSet G S hS ∪ isolateSet G S).card := by
        rw [Finset.card_union_of_disjoint hd.2.1,Finset.card_union_of_disjoint hd.1]
      _ = S.card := congrArg Finset.card hroles
  have hI : isolateSet G S = DegreeCapacity.isolates G S := by
    ext v
    change v ∈ S.filter (Isolate G S) ↔
      v ∈ S.filter (fun v => (S.filter (G.Adj v)).card = 0)
    rw [Finset.mem_filter,Finset.mem_filter]
    constructor
    · rintro ⟨hv,_,hi⟩
      refine ⟨hv,Finset.card_eq_zero.mpr ?_⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hi w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
    · rintro ⟨hv,hzero⟩
      refine ⟨hv,hv,?_⟩
      intro w hw hav
      have he := Finset.card_eq_zero.mp hzero
      have hm : w ∈ S.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hw,hav⟩
      rw [he] at hm
      exact Finset.notMem_empty _ hm
  have hA := filter_bool_sum (activeSet G S hS) color
  have hIs := filter_bool_sum (isolateSet G S) color
  have hFs := filter_bool_sum (witnessSet G S hS) color
  have hnfalse (v : V) : (color v ≠ false) ↔ color v = true := by cases color v <;> simp
  have hntrue (v : V) : (color v ≠ true) ↔ color v = false := by cases color v <;> simp
  rw [card_exchange,card_exchange]
  simp_rw [hnfalse,hntrue]
  rw [← hI]
  omega

/-- Isolate compensation holds for every finite bipartite graph, without a
regularity, connectivity or nonempty-selection hypothesis. -/
theorem selection_compensation (hG : G.Colorable 2)
    (S : Finset V) (hS : IsMinimalStarForming G 2 S) :
    2 * S.card ≤ 2 * beta G 2 + (DegreeCapacity.isolates G S).card := by
  classical
  obtain ⟨C⟩ := hG
  let color : V → Bool := fun v => decide (C v = 1)
  have hc : ∀ v w, G.Adj v w → color v ≠ color w := by
    intro v w hvw he
    have hn := C.valid hvw
    have hcv := (C v).isLt
    have hcw := (C w).isLt
    have hvals : C v = C w := by
      apply Fin.ext
      by_cases hv : (C v).val = 1 <;> by_cases hw : (C w).val = 1 <;>
        simp [color,Fin.ext_iff,hv,hw] at he <;> omega
    exact hn hvals
  have hsum := exchange_card_sum G S color hc hS
  have h0 : (exchange G S hS color false).card ≤ beta G 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,
      exchange_dissociation G S color hc hS false⟩)
  have h1 : (exchange G S hS color true).card ≤ beta G 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,
      exchange_dissociation G S color hc hS true⟩)
  omega

end D5.S3.Combinatorics.Graph.StarForming.BipartiteExchange


