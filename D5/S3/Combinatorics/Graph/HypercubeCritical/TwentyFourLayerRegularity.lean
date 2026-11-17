/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.claim
   digest: Global fourth-layer neighborhood disjointness forces high-degree regularity in a bipartite twenty-four vertex graph. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Batteries.Tactic.OpenPrivate

/-! Abstract BFS counting under global fourth-layer neighborhood disjointness.
The cube realization of this structural hypothesis is a separate obligation;
this module does not resolve the external f2(Q9) problem. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity

open SimpleGraph GirthSliceCounting
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private endpoint_eq_of_short_paths three_walk_endpoint_injective
  degree_parts_union degree_parts_disjoint sum_degree_parts
  neighbor_parts_card from D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private side_high_neighbor_sum from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal
open private actual_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- D concerns full neighborhoods in the actual graph, uniformly over every root. -/
private def layerDisjoint (G : SimpleGraph V) : Prop :=
  ∀ x y z, y ≠ z → G.edist x y = 4 → G.edist x z = 4 →
    G.degree y = 3 → G.degree z = 3 →
    (∀ a ∈ G.neighborFinset y, G.edist x a = 3) →
    (∀ a ∈ G.neighborFinset z, G.edist x a = 3) →
    Disjoint (G.neighborFinset y) (G.neighborFinset z)

private def second (G : SimpleGraph V) (x : V) : Finset V :=
  (G.neighborFinset x).biUnion fun a => (G.neighborFinset a).erase x

private def third (G : SimpleGraph V) (x : V) : Finset V :=
  (second G x).biUnion fun b => G.neighborFinset b \ G.neighborFinset x

private lemma mem_second {x b : V} :
    b ∈ second G x ↔ ∃ a, G.Adj x a ∧ G.Adj a b ∧ b ≠ x := by
  simp [second, Finset.mem_biUnion, and_left_comm, and_comm]

private lemma second_parent_unique (hg : (8 : ℕ∞) ≤ G.egirth)
    {x a a' b : V} (hxa : G.Adj x a) (hab : G.Adj a b)
    (hxa' : G.Adj x a') (ha'b : G.Adj a' b) (hbx : b ≠ x) : a = a' := by
  let p : G.Walk x b := .cons hxa (.cons hab .nil)
  let q : G.Walk x b := .cons hxa' (.cons ha'b .nil)
  have hp : p.IsPath := by simp [p, Walk.cons_isPath_iff, hbx.symm, hxa.ne, hab.ne]
  have hq : q.IsPath := by simp [q, Walk.cons_isPath_iff, hbx.symm, hxa'.ne, ha'b.ne]
  have he := endpoint_eq_of_short_paths hg hp hq (by simp [p, q])
  have hs := congrArg Walk.support he
  simpa [p, q] using hs

private lemma second_side {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x : V} (hx : x ∈ L) : second G x ⊆ L := by
  intro b hb
  obtain ⟨a, hxa, hab, _⟩ := mem_second.mp hb
  exact hpart.symm.mem_of_mem_adj (hpart.mem_of_mem_adj hx hxa) hab

private lemma root_not_second (x : V) : x ∉ second G x := by
  simp [mem_second]

private lemma second_card (hg : (8 : ℕ∞) ≤ G.egirth)
    {x : V} (hx : G.degree x = 3)
    (hhigh : ∀ a ∈ G.neighborFinset x, G.degree a = 3) :
    (second G x).card = 6 := by
  have hd : (↑(G.neighborFinset x) : Set V).PairwiseDisjoint
      (fun a => (G.neighborFinset a).erase x) := by
    intro a ha a' ha' hne
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    have hm := Finset.mem_erase.mp hb
    have hm' := Finset.mem_erase.mp hb'
    exact hne (second_parent_unique hg (by simpa using ha) (by simpa using hm.2)
      (by simpa using ha') (by simpa using hm'.2) hm.1)
  rw [second, Finset.card_biUnion hd]
  have he (a : V) (ha : a ∈ G.neighborFinset x) :
      ((G.neighborFinset a).erase x).card = 2 := by
    have hm : x ∈ G.neighborFinset a := by simpa using ((G.mem_neighborFinset _ _).mp ha).symm
    have hc := Finset.card_erase_add_one hm
    rw [G.card_neighborFinset_eq_degree, hhigh a ha] at hc
    omega
  calc
    _ = ∑ _a ∈ G.neighborFinset x, 2 := Finset.sum_congr rfl he
    _ = 6 := by simp [hx]

private lemma second_neighbor_inter (hg : (8 : ℕ∞) ≤ G.egirth)
    {x b : V} (hb : b ∈ second G x) :
    ((G.neighborFinset b) ∩ G.neighborFinset x).card = 1 := by
  obtain ⟨a, hxa, hab, hbx⟩ := mem_second.mp hb
  have he : G.neighborFinset b ∩ G.neighborFinset x = {a} := by
    ext a'
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hba', hxa'⟩
      exact second_parent_unique hg hxa' hba'.symm hxa hab hbx
    · rintro rfl
      exact ⟨hab.symm, hxa⟩
  simp [he]

private lemma third_witness {x c : V} (hc : c ∈ third G x) :
    ∃ a b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b c ∧ x ≠ b ∧ a ≠ c ∧
      b ∈ second G x ∧ c ∉ G.neighborFinset x := by
  obtain ⟨b, hb, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨a, hxa, hab, hbx⟩ := mem_second.mp hb
  have hm := Finset.mem_sdiff.mp hc
  refine ⟨a, b, hxa, hab, by simpa using hm.1, hbx.symm, ?_, hb, hm.2⟩
  intro he
  subst c
  exact hm.2 (by simpa using hxa)

private lemma third_side {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x : V} (hx : x ∈ L) : third G x ⊆ R := by
  intro c hc
  obtain ⟨a, b, _, _, hbc, _, _, hb, _⟩ := third_witness hc
  exact hpart.mem_of_mem_adj (second_side hpart hx hb) hbc

private lemma first_third_disjoint (x : V) :
    Disjoint (G.neighborFinset x) (third G x) := by
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  exact (third_witness hc').choose_spec.choose_spec.2.2.2.2.2.2 hc

private lemma third_parent_unique {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {x : V} (hx : x ∈ L)
    {b b' c : V} (hb : b ∈ second G x) (hb' : b' ∈ second G x)
    (hbc : G.Adj b c) (hb'c : G.Adj b' c) (hc : c ∉ G.neighborFinset x) : b = b' := by
  obtain ⟨a, hxa, hab, hbx⟩ := mem_second.mp hb
  obtain ⟨a', hxa', ha'b', hb'x⟩ := mem_second.mp hb'
  have hac : a ≠ c := fun he => hc (he ▸ ((G.mem_neighborFinset _ _).mpr hxa))
  have ha'c : a' ≠ c := fun he => hc (he ▸ ((G.mem_neighborFinset _ _).mpr hxa'))
  exact (three_walk_endpoint_injective hpart hg hx hx hxa hab hbc hxa' ha'b' hb'c
    hbx.symm hac hb'x.symm ha'c ⟨rfl, rfl⟩).2.2.1

private lemma third_card {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3)
    (hhigh : ∀ a ∈ G.neighborFinset x, G.degree a = 3) :
    (third G x).card + (degreeTwo G (second G x)).card = 12 := by
  have hd : (↑(second G x) : Set V).PairwiseDisjoint
      (fun b => G.neighborFinset b \ G.neighborFinset x) := by
    intro b hb b' hb' hne
    apply Finset.disjoint_left.mpr
    intro c hc hc'
    have hm := Finset.mem_sdiff.mp hc
    have hm' := Finset.mem_sdiff.mp hc'
    exact hne (third_parent_unique hpart hg hxL hb hb'
      (by simpa using hm.1) (by simpa using hm'.1) hm.2)
  have hc (b : V) (hb : b ∈ second G x) :
      (G.neighborFinset b \ G.neighborFinset x).card + 1 = G.degree b := by
    have he := Finset.card_sdiff_add_card_inter (G.neighborFinset b) (G.neighborFinset x)
    simpa [second_neighbor_inter hg hb] using he
  have hs : (third G x).card + (second G x).card = ∑ b ∈ second G x, G.degree b := by
    rw [third, Finset.card_biUnion hd]
    have he := Finset.sum_congr rfl hc
    simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] using he
  have hp := congrArg Finset.card (degree_parts_union hdeg (second G x))
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint _)] at hp
  have hdSum := sum_degree_parts hdeg (second G x) (fun b => G.degree b)
  have hl : (∑ b ∈ degreeTwo G (second G x), G.degree b) =
      2 * (degreeTwo G (second G x)).card := by
    trans ∑ _b ∈ degreeTwo G (second G x), 2
    · exact Finset.sum_congr rfl (fun b hb => (Finset.mem_filter.mp hb).2)
    · simp [Nat.mul_comm]
  have hh : (∑ b ∈ degreeThree G (second G x), G.degree b) =
      3 * (degreeThree G (second G x)).card := by
    trans ∑ _b ∈ degreeThree G (second G x), 3
    · exact Finset.sum_congr rfl (fun b hb => (Finset.mem_filter.mp hb).2)
    · simp [Nat.mul_comm]
  have h6 := second_card hg hx hhigh
  omega

private lemma third_edist {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x : V} (hx : x ∈ L) {c : V} (hc : c ∈ third G x) : G.edist x c = 3 := by
  obtain ⟨a, b, hxa, hab, hbc, _, _, _, hn⟩ := third_witness hc
  have hu : G.edist x c ≤ (3 : ℕ) := by
    simpa using (Walk.cons hxa (.cons hab (.cons hbc .nil))).edist_le
  obtain ⟨k, hk, hkle⟩ := ENat.le_natCast_iff.mp hu
  have hxc : x ≠ c := fun he => Set.disjoint_left.mp hpart.disjoint
    hx (he ▸ third_side hpart hx hc)
  have h0 : k ≠ 0 := by intro he; exact hxc (G.edist_eq_zero_iff.mp (by simpa [he] using hk))
  have h1 : k ≠ 1 := by intro he; exact hn ((G.mem_neighborFinset _ _).mpr
    (G.edist_eq_one_iff_adj.mp (by simpa [he] using hk)))
  have h2 : k ≠ 2 := by
    intro he
    obtain ⟨_, _, d, hd⟩ := G.edist_eq_two_iff.mp (by simpa [he] using hk)
    have hd' := G.mem_commonNeighbors.mp hd
    have hdR := hpart.mem_of_mem_adj hx hd'.1
    have hcL := hpart.symm.mem_of_mem_adj hdR hd'.2.symm
    exact Set.disjoint_left.mp hpart.disjoint hcL (third_side hpart hx hc)
  have : k = 3 := by omega
  simpa [this] using hk

private lemma fourth_edist (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    {x y : V} (hall : ∀ a ∈ G.neighborFinset y, G.edist x a = 3) :
    G.edist x y = 4 := by
  have hp : 0 < G.degree y := by rcases hdeg y with h | h <;> omega
  obtain ⟨a, hya⟩ := (G.degree_pos_iff_exists_adj y).mp hp
  have ha := hall a ((G.mem_neighborFinset _ _).mpr hya)
  have hu : G.edist x y ≤ (4 : ℕ) := by
    have ht := G.edist_triangle (u := x) (v := a) (w := y)
    rw [ha, G.edist_eq_one_iff_adj.mpr hya.symm] at ht
    exact ht
  obtain ⟨k, hk, hkle⟩ := ENat.le_natCast_iff.mp hu
  obtain ⟨p, hpk⟩ := G.exists_walk_of_edist_eq_coe (by rw [G.edist_comm]; exact hk)
  have hlow : 4 ≤ p.length := by
    cases p with
    | nil =>
      have he := G.edist_eq_one_iff_adj.mpr hya
      rw [ha] at he
      norm_num at he
    | @cons _ z _ hzy tail =>
      have hz := hall z ((G.mem_neighborFinset _ _).mpr hzy)
      have ht := tail.edist_le
      rw [G.edist_comm, hz] at ht
      have ht' : 3 ≤ tail.length := ENat.natCast_le_natCast.mp ht
      simp only [Walk.length_cons]
      omega
  have : k = 4 := by omega
  simpa [this] using hk

private lemma capacity (hD : layerDisjoint G)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (x : V) (A U : Finset V)
    (hh : ∀ y ∈ A, G.degree y = 3)
    (hlayer : ∀ y ∈ A, ∀ a ∈ G.neighborFinset y, G.edist x a = 3)
    (hsub : ∀ y ∈ A, G.neighborFinset y ⊆ U) : 3 * A.card ≤ U.card := by
  have hd : (↑A : Set V).PairwiseDisjoint (fun y => G.neighborFinset y) := by
    intro y hy z hz hne
    exact hD x y z hne (fourth_edist hdeg (hlayer y hy))
      (fourth_edist hdeg (hlayer z hz)) (hh y hy) (hh z hz)
      (hlayer y hy) (hlayer z hz)
  have hc : (A.biUnion fun y => G.neighborFinset y).card = 3 * A.card := by
    rw [Finset.card_biUnion hd]
    trans ∑ _y ∈ A, 3
    · apply Finset.sum_congr rfl
      intro y hy
      simpa using hh y hy
    · simp [Nat.mul_comm]
  rw [← hc]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨y, hy, hya⟩ := Finset.mem_biUnion.mp ha
  exact hsub y hy hya

private def outer (G : SimpleGraph V) (L : Finset V) (x : V) : Finset V :=
  L \ insert x (second G x)

private def omitted (G : SimpleGraph V) (R : Finset V) (x : V) : Finset V :=
  R \ (G.neighborFinset x ∪ third G x)

private lemma outer_not_adj_first {x y a : V} {L : Finset V}
    (hy : y ∈ outer G L x) (ha : a ∈ G.neighborFinset x) : ¬ G.Adj y a := by
  intro hya
  have hm := Finset.mem_sdiff.mp hy
  have hyx : y ≠ x := fun he => hm.2 (by simp [he])
  have hs : y ∈ second G x := mem_second.mpr
    ⟨a, by simpa using ha, hya.symm, hyx⟩
  exact hm.2 (Finset.mem_insert_of_mem hs)

private lemma outer_neighbors {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x y : V} (hy : y ∈ outer G L x) :
    G.neighborFinset y ⊆ third G x ∪ omitted G R x := by
  intro a ha
  have haR : a ∈ R := hpart.mem_of_mem_adj (Finset.mem_sdiff.mp hy).1 (by simpa using ha)
  have hn : a ∉ G.neighborFinset x := fun hn =>
    outer_not_adj_first hy hn (by simpa using ha)
  by_cases ht : a ∈ third G x
  · exact Finset.mem_union_left _ ht
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨haR, by simpa only [Finset.mem_union, not_or] using And.intro hn ht⟩)

private lemma omitted_neighbors {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x q : V} (hq : q ∈ omitted G R x) :
    G.neighborFinset q ⊆ outer G L x := by
  intro y hy
  have hm := Finset.mem_sdiff.mp hq
  have hn : q ∉ G.neighborFinset x := fun h => hm.2 (Finset.mem_union_left _ h)
  have ht : q ∉ third G x := fun h => hm.2 (Finset.mem_union_right _ h)
  have hqy : G.Adj q y := by simpa using hy
  refine Finset.mem_sdiff.mpr ⟨hpart.symm.mem_of_mem_adj hm.1 hqy, ?_⟩
  intro hi
  rcases Finset.mem_insert.mp hi with he | hs
  · subst y
    exact hn (by simpa using hqy.symm)
  · exact ht (Finset.mem_biUnion.mpr ⟨y, hs,
      Finset.mem_sdiff.mpr ⟨by simpa using hqy.symm, hn⟩⟩)

private lemma outer_card {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hL : L.card = 12)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3)
    (hhigh : ∀ a ∈ G.neighborFinset x, G.degree a = 3) :
    (outer G L x).card = 5 := by
  have hsub : insert x (second G x) ⊆ L := Finset.insert_subset hxL (second_side hpart hxL)
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_insert_of_notMem (root_not_second x), second_card hg hx hhigh, hL] at hc
  exact (by omega : (L \ insert x (second G x)).card = 5)

private lemma omitted_card {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V)) (hR : R.card = 12)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3) :
    (omitted G R x).card + (third G x).card + 3 = 12 := by
  have hsub : G.neighborFinset x ∪ third G x ⊆ R := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hpart.mem_of_mem_adj hxL (by simpa using ha)
    · exact third_side hpart hxL ha
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint (first_third_disjoint x),
    G.card_neighborFinset_eq_degree, hx, hR] at hc
  change (R \ (G.neighborFinset x ∪ third G x)).card + (third G x).card + 3 = 12
  omega

private lemma outer_low_card {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hL2 : (degreeTwo G L).card = 4)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3) :
    (degreeTwo G (second G x)).card + (degreeTwo G (outer G L x)).card = 4 := by
  have he : degreeTwo G L = degreeTwo G (second G x) ∪ degreeTwo G (outer G L x) := by
    ext y
    simp only [degreeTwo, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hy, hy2⟩
      by_cases hs : y ∈ second G x
      · exact Or.inl ⟨hs, hy2⟩
      · right
        refine ⟨Finset.mem_sdiff.mpr ⟨hy, ?_⟩, hy2⟩
        simp only [Finset.mem_insert, not_or]
        refine ⟨?_, hs⟩
        intro he
        subst y
        omega
    · rintro (⟨hy, hy2⟩ | ⟨hy, hy2⟩)
      · exact ⟨second_side hpart hxL hy, hy2⟩
      · exact ⟨(Finset.mem_sdiff.mp hy).1, hy2⟩
  have hd : Disjoint (degreeTwo G (second G x)) (degreeTwo G (outer G L x)) := by
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy').1).2
      (Finset.mem_insert_of_mem (Finset.mem_filter.mp hy).1)
  rw [he, Finset.card_union_of_disjoint hd] at hL2
  exact hL2

/-- Every high root with three high neighbors sees all four same-side lows in
its actual second layer. The global D hypothesis is used for the b=3 branch. -/
private lemma all_lows_second {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hD : layerDisjoint G)
    (hL : L.card = 12) (hR : R.card = 12) (hL2 : (degreeTwo G L).card = 4)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3)
    (hhigh : ∀ a ∈ G.neighborFinset x, G.degree a = 3) :
    degreeTwo G L ⊆ second G x := by
  have hs := third_card hpart hg hdeg hxL hx hhigh
  have ho := omitted_card hpart hR hxL hx
  have hw := outer_card hpart hg hL hxL hx hhigh
  have hl := outer_low_card hpart hL2 hxL hx
  have hp := congrArg Finset.card (degree_parts_union hdeg (outer G L x))
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint _)] at hp
  have hb : (degreeTwo G (second G x)).card = 3 ∨
      (degreeTwo G (second G x)).card = 4 := by omega
  have hb4 : (degreeTwo G (second G x)).card = 4 := by
    rcases hb with hb | hb
    · have he : omitted G R x = ∅ := Finset.card_eq_zero.mp (by omega)
      have hn (y : V) (hy : y ∈ degreeThree G (outer G L x)) :
          G.neighborFinset y ⊆ third G x := by
        have hu := outer_neighbors hpart (Finset.mem_filter.mp hy).1
        simpa [he] using hu
      have hc := capacity hD hdeg x (degreeThree G (outer G L x)) (third G x)
        (fun y hy => (Finset.mem_filter.mp hy).2)
        (fun y hy a ha => third_edist hpart hxL (hn y hy ha)) hn
      omega
    · exact hb
  have he : degreeTwo G (outer G L x) = ∅ := Finset.card_eq_zero.mp (by omega)
  intro y hy
  have hm := Finset.mem_filter.mp hy
  by_contra hn
  have hyx : y ≠ x := by intro he; subst y; omega
  have how : y ∈ outer G L x := Finset.mem_sdiff.mpr
    ⟨hm.1, by simp only [Finset.mem_insert, not_or]; exact ⟨hyx, hn⟩⟩
  have : y ∈ degreeTwo G (outer G L x) := Finset.mem_filter.mpr ⟨how, hm.2⟩
  simp [he] at this

private lemma no_three_high {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hD : layerDisjoint G)
    (hL : L.card = 12) (hR : R.card = 12)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3)
    (hhigh : ∀ a ∈ G.neighborFinset x, G.degree a = 3) : False := by
  have hlow2 := all_lows_second hpart hdeg hg hD hL hR hL2 hxL hx hhigh
  have he : degreeTwo G (second G x) = degreeTwo G L := by
    ext y
    simp only [degreeTwo, Finset.mem_filter]
    exact ⟨fun h => ⟨second_side hpart hxL h.1, h.2⟩,
      fun h => ⟨hlow2 (Finset.mem_filter.mpr h), h.2⟩⟩
  have hb : (degreeTwo G (second G x)).card = 4 := by rw [he, hL2]
  have hs : (third G x).card = 8 := by
    have := third_card hpart hg hdeg hxL hx hhigh
    omega
  have hw : (outer G L x).card = 5 := outer_card hpart hg hL hxL hx hhigh
  have hWhigh (y : V) (hy : y ∈ outer G L x) : G.degree y = 3 := by
    rcases hdeg y with hy2 | hy3
    · have hyS := hlow2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy).1, hy2⟩)
      exact False.elim ((Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hyS))
    · exact hy3
  have hQ : (omitted G R x).card = 1 := by
    have := omitted_card hpart hR hxL hx
    omega
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hQ
  have hqQ : q ∈ omitted G R x := by rw [hq]; simp
  have hqR : q ∈ R := (Finset.mem_sdiff.mp hqQ).1
  have hU : G.neighborFinset q ⊆ outer G L x := omitted_neighbors hpart hqQ
  let T := outer G L x \ G.neighborFinset q
  have hTcard : T.card + G.degree q = 5 := by
    simpa only [G.card_neighborFinset_eq_degree, hw] using Finset.card_sdiff_add_card_eq_card hU
  have hThigh (t : V) (ht : t ∈ T) : G.degree t = 3 :=
    hWhigh t (Finset.mem_sdiff.mp ht).1
  have hTN (t : V) (ht : t ∈ T) : G.neighborFinset t ⊆ third G x := by
    intro a ha
    rcases Finset.mem_union.mp (outer_neighbors hpart (Finset.mem_sdiff.mp ht).1 ha) with haS | haQ
    · exact haS
    · have haq : a = q := by simpa only [hq, Finset.mem_singleton] using haQ
      subst a
      exact False.elim ((Finset.mem_sdiff.mp ht).2
        (by simpa using ((G.mem_neighborFinset _ _).mp ha).symm))
  have hTcap := capacity hD hdeg x T (third G x) hThigh
    (fun t ht a ha => third_edist hpart hxL (hTN t ht ha)) hTN
  have hq3 : G.degree q = 3 := by
    rcases hdeg q with h2 | h3
    · omega
    · exact h3
  have hqhigh (u : V) (hu : u ∈ G.neighborFinset q) : G.degree u = 3 := hWhigh u (hU hu)
  have hqLow := all_lows_second hpart.symm hdeg hg hD hR hL hR2 hqR hq3 hqhigh
  have hTNhigh (t : V) (ht : t ∈ T) : G.neighborFinset t ⊆ degreeThree G (third G x) := by
    intro c hc
    have hcS := hTN t ht hc
    refine Finset.mem_filter.mpr ⟨hcS, ?_⟩
    rcases hdeg c with hc2 | hc3
    · have hcSq := hqLow (Finset.mem_filter.mpr ⟨third_side hpart hxL hcS, hc2⟩)
      obtain ⟨u, hqu, huc, _⟩ := mem_second.mp hcSq
      obtain ⟨a, b, _, _, hbc, _, _, hbS, _⟩ := third_witness hcS
      have huU : u ∈ G.neighborFinset q := by simpa using hqu
      have huW := hU huU
      have htb : t ≠ b := by
        intro he
        subst t
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ht).1).2 (Finset.mem_insert_of_mem hbS)
      have htu : t ≠ u := by
        intro he
        subst t
        exact (Finset.mem_sdiff.mp ht).2 huU
      have hbu : b ≠ u := by
        intro he
        subst b
        exact (Finset.mem_sdiff.mp huW).2 (Finset.mem_insert_of_mem hbS)
      have hsub : ({t, b, u} : Finset V) ⊆ G.neighborFinset c := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · simpa using ((G.mem_neighborFinset _ _).mp hc).symm
        · simpa using hbc.symm
        · simpa using huc.symm
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_triple_eq_three_iff.mpr ⟨htb, htu, hbu⟩,
        G.card_neighborFinset_eq_degree, hc2] at hcard
      omega
    · exact hc3
  have hlows : degreeTwo G R ⊆ third G x := by
    intro c hc
    have hm := Finset.mem_filter.mp hc
    have hcn : c ∉ G.neighborFinset x := by
      intro hn
      have := hhigh c hn
      omega
    by_contra hn
    have hcQ : c ∈ omitted G R x := Finset.mem_sdiff.mpr
      ⟨hm.1, by simp only [Finset.mem_union, not_or]; exact ⟨hcn, hn⟩⟩
    have hcq : c = q := by simpa only [hq, Finset.mem_singleton] using hcQ
    subst c
    omega
  have hloweq : degreeTwo G (third G x) = degreeTwo G R := by
    ext c
    simp only [degreeTwo, Finset.mem_filter]
    exact ⟨fun h => ⟨third_side hpart hxL h.1, h.2⟩,
      fun h => ⟨hlows (Finset.mem_filter.mpr h), h.2⟩⟩
  have hp := congrArg Finset.card (degree_parts_union hdeg (third G x))
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint _), hloweq, hR2, hs] at hp
  have hc := capacity hD hdeg x T (degreeThree G (third G x)) hThigh
    (fun t ht a ha => third_edist hpart hxL (hTN t ht ha)) hTNhigh
  omega

private lemma high_degree_le_two {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hD : layerDisjoint G)
    (hL : L.card = 12) (hR : R.card = 12)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3) :
    (degreeThree G (G.neighborFinset x)).card ≤ 2 := by
  have hsub : degreeThree G (G.neighborFinset x) ⊆ G.neighborFinset x := Finset.filter_subset _ _
  have hle := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, hx] at hle
  by_contra hn
  have he : degreeThree G (G.neighborFinset x) = G.neighborFinset x :=
    Finset.eq_of_subset_of_card_le hsub (by simpa only [G.card_neighborFinset_eq_degree, hx] using (by omega : 3 ≤ (degreeThree G (G.neighborFinset x)).card))
  apply no_three_high hpart hdeg hg hD hL hR hL2 hR2 hxL hx
  intro a ha
  have : a ∈ degreeThree G (G.neighborFinset x) := by rw [he]; exact ha
  exact (Finset.mem_filter.mp this).2

private lemma side_regular {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hD : layerDisjoint G)
    (hL : L.card = 12) (hR : R.card = 12)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3) :
    (degreeThree G (G.neighborFinset x)).card = 2 := by
  have hpL := congrArg Finset.card (degree_parts_union hdeg L)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint _), hL2, hL] at hpL
  have hpR := congrArg Finset.card (degree_parts_union hdeg R)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint _), hR2, hR] at hpR
  have hs := side_high_neighbor_sum hpart.symm hdeg hlow
  have hsum : (∑ y ∈ degreeThree G L, (degreeThree G (G.neighborFinset y)).card) = 16 := by omega
  have hbound (y : V) (hy : y ∈ degreeThree G L) :
      (degreeThree G (G.neighborFinset y)).card ≤ 2 :=
    high_degree_le_two hpart hdeg hg hD hL hR hL2 hR2
      (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hsum2 : (∑ _y ∈ degreeThree G L, 2) = 16 := by simp; omega
  have heach := (Finset.sum_eq_sum_iff_of_le hbound).mp (hsum.trans hsum2.symm)
  exact heach x (Finset.mem_filter.mpr ⟨hxL, hx⟩)

/-- A genuine graph satisfying D but violating high-neighbor regularity. -/
def claim : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)),
    G.IsBipartiteWith (L : Set (Fin n)) (R : Set (Fin n)) ∧
    L.card = 12 ∧ R.card = 12 ∧
    (∀ v, G.degree v = 2 ∨ G.degree v = 3) ∧
    (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4 ∧
    (∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) ∧
    (8 : ℕ∞) ≤ G.egirth ∧ layerDisjoint G ∧
    ∃ v, G.degree v = 3 ∧ (degreeThree G (G.neighborFinset v)).card ≠ 2

/-- D forces every full-degree-three vertex to have exactly two full-degree-three neighbors. -/
theorem result : ¬ claim := by
  rintro ⟨n, G, L, R, hpart, hL, hR, hdeg, hL2, hR2, hlow, hg, hD, v, hv, hn⟩
  rcases actual_partition hpart hdeg v with hvL | hvR
  · exact hn (side_regular hpart hdeg hlow hg hD hL hR hL2 hR2 hvL hv)
  · exact hn (side_regular hpart.symm hdeg hlow hg hD hR hL hR2 hL2 hvR hv)

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
