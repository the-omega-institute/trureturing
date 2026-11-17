/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: A bipartite graph on fifteen vertices, with degrees two or three, nine independent degree-two vertices and girth at least eight, is a once-subdivided K3,3. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import Batteries.Tactic.OpenPrivate

/-! Girth turns the actual two-neighbor middles into a simple triangle-free cubic
core; its exact bipartition determines every original incidence. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure

open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open private one_three_cross_impossible three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private parts_card sum_degrees_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

/-- An exact incidence description of the once-subdivision of K3,3. The six branch
vertices split into two triples; each pair across the triples has exactly one
middle vertex, and every middle vertex has precisely its two indicated neighbors. -/
def IsK33Subdivision (G : SimpleGraph V) : Prop :=
  ∃ L R : Finset V,
    G.IsBipartiteWith (L : Set V) (R : Set V) ∧ L ∪ R = Finset.univ ∧
    L.card = 6 ∧ R.card = 9 ∧
    (∀ x ∈ L, G.degree x = 3) ∧ (∀ m ∈ R, G.degree m = 2) ∧
    ∃ A B : Finset (L : Set V),
      A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      (∀ a ∈ A, ∀ b ∈ B, ∃! m, m ∈ R ∧ G.Adj a.val m ∧ G.Adj b.val m) ∧
      (∀ m ∈ R, ∃ a ∈ A, ∃ b ∈ B, G.neighborFinset m = {a.val, b.val})

private theorem two_neighbor_table {m x : V} (hm : G.degree m = 2)
    (hxm : G.Adj x m) :
    ∃ y, y ≠ x ∧ G.Adj y m ∧ G.neighborFinset m = {x, y} := by
  classical
  have hc : 1 < (G.neighborFinset m).card := by
    rw [G.card_neighborFinset_eq_degree, hm]
    decide
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne hc x
  refine ⟨y, hyx, ((G.mem_neighborFinset m y).mp hy).symm, ?_⟩
  have hs : ({x, y} : Finset V) ⊆ G.neighborFinset m := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨(G.mem_neighborFinset m x).mpr hxm.symm, hy⟩
  exact (Finset.eq_of_subset_of_card_le hs (by
    simp [G.card_neighborFinset_eq_degree, hm, hyx.symm])).symm

private theorem middle_unique
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {x y m n : V}
    (hx : x ∈ L) (hxy : x ≠ y)
    (hxm : G.Adj x m) (hym : G.Adj y m)
    (hxn : G.Adj x n) (hyn : G.Adj y n) : m = n := by
  by_contra hmn
  exact one_three_cross_impossible hpart hg hx hx
    hxn hxm hym.symm hyn hxy hmn ⟨rfl, rfl⟩

/-- Two low vertices cannot both use the same two opposite high vertices. -/
private theorem exclude_seven_eight
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL2 : (degreeTwo G L).card = 3) (hR3 : (degreeThree G R).card = 2) : False := by
  classical
  have hN (x : V) (hx : x ∈ degreeTwo G L) :
      G.neighborFinset x = degreeThree G R := by
    have hx2 := (Finset.mem_filter.mp hx).2
    have hs : G.neighborFinset x ⊆ degreeThree G R := by
      intro y hy
      have hxy := (G.mem_neighborFinset x y).mp hy
      have hyR : y ∈ R := hpart.mem_of_mem_adj (Finset.mem_filter.mp hx).1 hxy
      have hy3 : G.degree y = 3 := by
        rcases hdeg y with hy2 | hy3
        · exact (hlow hxy hx2 hy2).elim
        · exact hy3
      exact Finset.mem_filter.mpr ⟨hyR, hy3⟩
    exact Finset.eq_of_subset_of_card_le hs (by
      rw [hR3, G.card_neighborFinset_eq_degree, hx2])
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (degreeTwo G L).card)
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < (degreeTwo G L).card) x
  obtain ⟨m, n, hmn, hmnR⟩ := Finset.card_eq_two.mp hR3
  have ha (z : V) (hz : z ∈ degreeTwo G L) : G.Adj z m ∧ G.Adj z n := by
    constructor <;> apply (G.mem_neighborFinset z _).mp <;> rw [hN z hz, hmnR] <;> simp
  have hm := middle_unique hpart hg (Finset.mem_filter.mp hx).1 hyx.symm
    (ha x hx).1 (ha y hy).1 (ha x hx).2 (ha y hy).2
  exact hmn hm

/-- The degree balance has four ordered solutions; the two mixed solutions
are excluded using actual adjacency, rather than discarded arithmetically. -/
private theorem orient_sides
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcover : L ∪ R = Finset.univ)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hV : Fintype.card V = 15) (hq : (degreeTwo G Finset.univ).card = 9) :
    (L.card = 6 ∧ R.card = 9 ∧ (degreeTwo G L).card = 0 ∧ (degreeTwo G R).card = 9) ∨
    (R.card = 6 ∧ L.card = 9 ∧ (degreeTwo G R).card = 0 ∧ (degreeTwo G L).card = 9) := by
  classical
  have hdisj : Disjoint L R := by
    simpa only [Finset.disjoint_coe] using hpart.disjoint
  have hN : L.card + R.card = 15 := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ, hV]
  have hd : Disjoint (degreeTwo G L) (degreeTwo G R) :=
    hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hpq : (degreeTwo G L).card + (degreeTwo G R).card = 9 := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa only [degreeTwo, ← Finset.filter_union, hcover] using hq
  have hLp := parts_card G hdeg L
  have hRp := parts_card G hdeg R
  have he := SimpleGraph.isBipartiteWith_sum_degrees_eq (s := L) (t := R) hpart
  rw [sum_degrees_parts G hdeg L, sum_degrees_parts G hdeg R] at he
  have hp : (degreeTwo G L).card = 0 ∨ (degreeTwo G L).card = 3 ∨
      (degreeTwo G L).card = 6 ∨ (degreeTwo G L).card = 9 := by omega
  rcases hp with hp | hp | hp | hp
  · exact Or.inl ⟨by omega, by omega, hp, by omega⟩
  · exact (exclude_seven_eight hpart hdeg hlow hg hp (by omega)).elim
  · exact (exclude_seven_eight hpart.symm hdeg hlow hg (by omega) (by omega)).elim
  · exact Or.inr ⟨by omega, by omega, by omega, hp⟩

private def core (G : SimpleGraph V) (L R : Finset V) : SimpleGraph (L : Set V) where
  Adj x y := x ≠ y ∧ ∃ m ∈ R, G.Adj x.val m ∧ G.Adj y.val m
  symm := ⟨fun _ _ h => by
    obtain ⟨hne, m, hm, hxm, hym⟩ := h
    exact ⟨hne.symm, m, hm, hym, hxm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem other_left
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hright : ∀ m ∈ R, G.degree m = 2)
    (x : (L : Set V)) {m : V} (hm : m ∈ R) (hxm : G.Adj x.val m) :
    ∃ y : (L : Set V), y ≠ x ∧ G.Adj y.val m ∧
      G.neighborFinset m = {x.val, y.val} := by
  obtain ⟨y, hyx, hym, hN⟩ := two_neighbor_table (hright m hm) hxm
  have hyL : y ∈ L := hpart.mem_of_mem_adj' hm hym
  exact ⟨⟨y, hyL⟩, fun h => hyx (congrArg Subtype.val h), hym, hN⟩

private theorem core_degree_three
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hleft : ∀ x ∈ L, G.degree x = 3)
    (hright : ∀ m ∈ R, G.degree m = 2) :
    ∀ x, (core G L R).degree x = 3 := by
  classical
  intro x
  have ho (m : V) (hm : m ∈ G.neighborFinset x.val) :
      ∃ y : (L : Set V), y ≠ x ∧ G.Adj y.val m ∧
        G.neighborFinset m = {x.val, y.val} :=
    other_left hpart hright x (hpart.mem_of_mem_adj x.property
      ((G.mem_neighborFinset _ _).mp hm)) ((G.mem_neighborFinset _ _).mp hm)
  have hc : (G.neighborFinset x.val).card = ((core G L R).neighborFinset x).card := by
    apply Finset.card_bij (fun m hm => Classical.choose (ho m hm))
    · intro m hm
      have hy := Classical.choose_spec (ho m hm)
      exact ((core G L R).mem_neighborFinset _ _).mpr
        ⟨hy.1.symm, m, hpart.mem_of_mem_adj x.property
          ((G.mem_neighborFinset _ _).mp hm), (G.mem_neighborFinset _ _).mp hm, hy.2.1⟩
    · intro m hm n hn he
      have hy := Classical.choose_spec (ho m hm)
      have hz := Classical.choose_spec (ho n hn)
      have hzn : G.Adj (Classical.choose (ho m hm)).val n := by
        simpa only [he] using hz.2.1
      exact middle_unique hpart hg x.property
        (fun hv => hy.1 (Subtype.ext hv).symm)
        ((G.mem_neighborFinset _ _).mp hm) hy.2.1
        ((G.mem_neighborFinset _ _).mp hn) hzn
    · intro y hy
      obtain ⟨hxy, m, hmR, hxm, hym⟩ := ((core G L R).mem_neighborFinset _ _).mp hy
      have hm : m ∈ G.neighborFinset x.val := (G.mem_neighborFinset _ _).mpr hxm
      have hz := Classical.choose_spec (ho m hm)
      have hymem : y.val ∈ G.neighborFinset m := (G.mem_neighborFinset _ _).mpr hym.symm
      rw [hz.2.2] at hymem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
      rcases hymem with he | he
      · exact (hxy (Subtype.ext he).symm).elim
      · exact ⟨m, hm, (Subtype.ext he).symm⟩
  rw [SimpleGraph.degree, ← hc, G.card_neighborFinset_eq_degree]
  exact hleft x.val x.property

private theorem middle_third
    (hright : ∀ m ∈ R, G.degree m = 2)
    {x y z : (L : Set V)} {m : V} (hm : m ∈ R) (hxy : x ≠ y)
    (hxm : G.Adj x.val m) (hym : G.Adj y.val m) (hzm : G.Adj z.val m) :
    z = x ∨ z = y := by
  classical
  have hxyV : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hs : ({x.val, y.val} : Finset V) ⊆ G.neighborFinset m := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨(G.mem_neighborFinset _ _).mpr hxm.symm,
      (G.mem_neighborFinset _ _).mpr hym.symm⟩
  have hN : G.neighborFinset m = {x.val, y.val} :=
    (Finset.eq_of_subset_of_card_le hs (by
      simp [G.card_neighborFinset_eq_degree, hright m hm, hxyV])).symm
  have hz := (G.mem_neighborFinset _ _).mpr hzm.symm
  rw [hN] at hz
  simpa only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] using hz

private theorem core_triangle_free
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hright : ∀ m ∈ R, G.degree m = 2) :
    ∀ x y z, (core G L R).Adj x y → (core G L R).Adj y z →
      (core G L R).Adj z x → False := by
  intro x y z hxy hyz hzx
  obtain ⟨hxy, a, ha, hxa, hya⟩ := hxy
  obtain ⟨hyz, b, hb, hyb, hzb⟩ := hyz
  obtain ⟨hzx, c, hc, hzc, hxc⟩ := hzx
  have hab : a ≠ b := by
    intro he
    have hza : G.Adj z.val a := he ▸ hzb
    rcases middle_third hright ha hxy hxa hya hza with h | h
    · exact hzx h
    · exact hyz h.symm
  have hcb : c ≠ b := by
    intro he
    have hyc : G.Adj y.val c := he ▸ hyb
    rcases middle_third hright hc hzx hzc hxc hyc with h | h
    · exact hyz h
    · exact hxy h.symm
  have hac : a ≠ c := by
    intro he
    have hza : G.Adj z.val a := he ▸ hzc
    rcases middle_third hright ha hxy hxa hya hza with h | h
    · exact hzx h
    · exact hyz h.symm
  have he := three_walk_endpoint_injective hpart hg x.property x.property
    hxa hya.symm hyb hxc hzc.symm hzb
    (fun h => hxy (Subtype.ext h)) hab (fun h => hzx (Subtype.ext h).symm) hcb ⟨rfl, rfl⟩
  exact hac he.2.1

private theorem cubic_six_bipartition
    {W : Type*} [Fintype W] [DecidableEq W] (F : SimpleGraph W)
    (hW : Fintype.card W = 6) (hdeg : ∀ w, F.degree w = 3)
    (htri : ∀ x y z, F.Adj x y → F.Adj y z → F.Adj z x → False) :
    ∃ A B : Finset W,
      A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      ∀ x y, F.Adj x y ↔ (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A) := by
  classical
  haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let u : W := Classical.arbitrary W
  let B := F.neighborFinset u
  let A := Finset.univ \ B
  have hB : B.card = 3 := hdeg u
  have hA : A.card = 3 := by
    simp only [A, Finset.card_sdiff_of_subset (Finset.subset_univ B),
      Finset.card_univ, hW, hB]
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 hxB
  have hcover : A ∪ B = Finset.univ :=
    Finset.sdiff_union_of_subset (Finset.subset_univ B)
  have hNB (b : W) (hb : b ∈ B) : F.neighborFinset b = A := by
    have hub : F.Adj u b := (F.mem_neighborFinset _ _).mp hb
    have hs : F.neighborFinset b ⊆ A := by
      intro z hz
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hzB
      exact htri u b z hub ((F.mem_neighborFinset _ _).mp hz)
        ((F.mem_neighborFinset _ _).mp hzB).symm
    exact Finset.eq_of_subset_of_card_le hs (by
      rw [hA, F.card_neighborFinset_eq_degree, hdeg])
  have hNA (a : W) (ha : a ∈ A) : F.neighborFinset a = B := by
    have hs : B ⊆ F.neighborFinset a := by
      intro b hb
      apply (F.mem_neighborFinset _ _).mpr
      exact ((F.mem_neighborFinset _ _).mp (by rw [hNB b hb]; exact ha)).symm
    exact (Finset.eq_of_subset_of_card_le hs (by
      rw [hB, F.card_neighborFinset_eq_degree, hdeg])).symm
  refine ⟨A, B, hA, hB, hdisj, hcover, ?_⟩
  intro x y
  constructor
  · intro hxy
    have hx : x ∈ A ∨ x ∈ B := by rw [← Finset.mem_union, hcover]; simp
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, by
        rw [← hNA x hx]
        exact (F.mem_neighborFinset _ _).mpr hxy⟩
    · exact Or.inr ⟨hx, by
        rw [← hNB x hx]
        exact (F.mem_neighborFinset _ _).mpr hxy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · apply (F.mem_neighborFinset _ _).mp
      rw [hNA x hx]
      exact hy
    · apply (F.mem_neighborFinset _ _).mp
      rw [hNB x hx]
      exact hy

private theorem oriented_subdivision
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcover : L ∪ R = Finset.univ)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 6) (hR : R.card = 9)
    (hL2 : (degreeTwo G L).card = 0) (hR2 : (degreeTwo G R).card = 9) :
    IsK33Subdivision G := by
  classical
  have hleft : ∀ x ∈ L, G.degree x = 3 := by
    intro x hx
    rcases hdeg x with hx2 | hx3
    · have hm : x ∈ degreeTwo G L := Finset.mem_filter.mpr ⟨hx, hx2⟩
      rw [Finset.card_eq_zero.mp hL2] at hm
      exact (Finset.notMem_empty x hm).elim
    · exact hx3
  have hright : ∀ m ∈ R, G.degree m = 2 := by
    have he : degreeTwo G R = R :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    intro m hm
    have hm2 : m ∈ degreeTwo G R := by rw [he]; exact hm
    exact (Finset.mem_filter.mp hm2).2
  have hcard : Fintype.card (L : Set V) = 6 := by simpa using hL
  obtain ⟨A, B, hA, hB, hd, hAB, hAdj⟩ := cubic_six_bipartition (core G L R)
    hcard (core_degree_three hpart hg hleft hright)
    (core_triangle_free hpart hg hright)
  refine ⟨L, R, hpart, hcover, hL, hR, hleft, hright, A, B, hA, hB, hd, hAB, ?_, ?_⟩
  · intro a ha b hb
    have hab := (hAdj a b).mpr (Or.inl ⟨ha, hb⟩)
    obtain ⟨hne, m, hm, ham, hbm⟩ := hab
    refine ⟨m, ⟨hm, ham, hbm⟩, ?_⟩
    intro n hn
    exact middle_unique hpart hg a.property
      (fun h => hne (Subtype.ext h)) hn.2.1 hn.2.2 ham hbm
  · intro m hm
    have hc : 0 < (G.neighborFinset m).card := by
      rw [G.card_neighborFinset_eq_degree, hright m hm]
      decide
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hc
    have hxm : G.Adj x m := ((G.mem_neighborFinset _ _).mp hx).symm
    let a : (L : Set V) := ⟨x, hpart.mem_of_mem_adj' hm hxm⟩
    obtain ⟨b, hba, hbm, hN⟩ := other_left hpart hright a hm hxm
    have hab : (core G L R).Adj a b := ⟨hba.symm, m, hm, hxm, hbm⟩
    rcases (hAdj a b).mp hab with ⟨haA, hbB⟩ | ⟨haB, hbA⟩
    · exact ⟨a, haA, b, hbB, hN⟩
    · exact ⟨b, hbA, a, haB, by simpa only [Finset.pair_comm] using hN⟩

/-- The degree and girth conditions force the entire incidence structure;
no connectedness, labels, suppression certificate or embedding is assumed. -/
theorem fifteen_vertex_subdivision
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcover : L ∪ R = Finset.univ)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hV : Fintype.card V = 15) (hq : (degreeTwo G Finset.univ).card = 9) :
    IsK33Subdivision G := by
  rcases orient_sides hpart hcover hdeg hlow hg hV hq with h | h
  · exact oriented_subdivision hpart hcover hdeg hg h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact oriented_subdivision hpart.symm (by simpa only [Finset.union_comm] using hcover)
      hdeg hg h.1 h.2.1 h.2.2.1 h.2.2.2

#print axioms fifteen_vertex_subdivision

end D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
