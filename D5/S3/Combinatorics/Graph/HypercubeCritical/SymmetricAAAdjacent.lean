/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricAAAdjacent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricAAAdjacent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: In the A/A high-degree profiles, actual low-pair deficits force the unique high leaves on opposite sides to be adjacent. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPairDeficit
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import Batteries.Tactic.OpenPrivate

/-! Adjacency of the unique actual high leaves in the A/A branch. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAAdjacent

open SimpleGraph GirthSliceCounting
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private lowPair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private highDegree highDeficit highTypeA highProfile symmetric_high_profiles from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
open private actual_low_pair_capacity cross_low_neighbors_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPairDeficit
open private unique_low_partner from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem nonadjacent_leaf_neighbor_low_pair
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL2 : (degreeTwo G L).card = 4)
    (hnonneg : ∀ x ∈ degreeThree G L, 0 ≤ highDeficit G x)
    {a b : V} (hbR : b ∈ R) (hb3 : G.degree b = 3)
    (hb1 : highDegree G b = 1)
    (hLa : ∀ z ∈ degreeThree G L, z ≠ a → highDegree G z = 2)
    (hRb : ∀ z ∈ degreeThree G R, z ≠ b → highDegree G z = 2)
    (hab : ¬ G.Adj a b) :
    ∃ x, x ∈ L ∧ G.degree x = 3 ∧ x ≠ a ∧ G.Adj x b ∧ lowPair G a x := by
  obtain ⟨x, hxN⟩ := Finset.card_pos.mp (show
      0 < (degreeThree G (G.neighborFinset b)).card by
    change 0 < highDegree G b
    omega)
  have hxb : G.Adj x b := ((G.mem_neighborFinset _ _).mp
    (Finset.mem_filter.mp hxN).1).symm
  have hx3 : G.degree x = 3 := (Finset.mem_filter.mp hxN).2
  have hxL : x ∈ L := hpart.symm.mem_of_mem_adj hbR hxb.symm
  have hxa : x ≠ a := by intro he; exact hab (he ▸ hxb)
  have hxmem : x ∈ degreeThree G L := Finset.mem_filter.mpr ⟨hxL, hx3⟩
  have hx2 := hLa x hxmem hxa
  obtain ⟨c, hcN, hcb⟩ := Finset.exists_mem_ne (show
      1 < (degreeThree G (G.neighborFinset x)).card by
    change 1 < highDegree G x
    omega) b
  have hxc : G.Adj x c := (G.mem_neighborFinset _ _).mp
    (Finset.mem_filter.mp hcN).1
  have hc3 : G.degree c = 3 := (Finset.mem_filter.mp hcN).2
  have hcR : c ∈ R := hpart.mem_of_mem_adj hxL hxc
  have hc2 := hRb c (Finset.mem_filter.mpr ⟨hcR, hc3⟩) hcb
  have hbN : b ∈ degreeThree G (G.neighborFinset x) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxb, hb3⟩
  have hN : degreeThree G (G.neighborFinset x) = {b, c} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hbN
      · exact Finset.mem_singleton.mp hz ▸ hcN
    · change highDegree G x ≤ _
      simp [hx2, hcb.symm]
  have hdx : highDeficit G x = 1 := by
    dsimp only [highDeficit]
    rw [hx2, hN]
    simp [hcb.symm, hb1, hc2]
  obtain ⟨w, z, hw2, hz3, hxz, hxw, hzw, _⟩ :=
    unique_low_partner hdeg hlow hx3 hx2
  have hzL : z ∈ L := hpart.symm.mem_of_mem_adj
    (hpart.mem_of_mem_adj hxL hxw) hzw.symm
  have hzmem : z ∈ degreeThree G L := Finset.mem_filter.mpr ⟨hzL, hz3⟩
  have hp : lowPair G x z := ⟨w, hw2, hxw, hzw⟩
  have hza : z = a := by
    by_contra hza
    have hz2 := hLa z hzmem hza
    have hzero := (actual_low_pair_capacity hpart hdeg hg hxL hzL hx3 hz3
      hxz hp).2.2 hL2
    have hdx0 := (hzero.2.2 hx2 hz2 (hnonneg x hxmem) (hnonneg z hzmem)).1
    omega
  subst z
  exact ⟨x, hxL, hx3, hxa, hxb, w, hw2, hzw, hxw⟩

/-- In an actual bipartite degree-two/three graph of girth at least eight,
four actual lows on each side and nonnegative high deficits force the two
unique high leaves to be adjacent when every other high point has high degree two. -/
private theorem actual_unique_high_leaves_adjacent
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLn : ∀ x ∈ degreeThree G L, 0 ≤ highDeficit G x)
    (hRn : ∀ x ∈ degreeThree G R, 0 ≤ highDeficit G x)
    {a b : V} (ha : a ∈ degreeThree G L) (hb : b ∈ degreeThree G R)
    (ha1 : highDegree G a = 1) (hb1 : highDegree G b = 1)
    (hLa : ∀ x ∈ degreeThree G L, x ≠ a → highDegree G x = 2)
    (hRb : ∀ x ∈ degreeThree G R, x ≠ b → highDegree G x = 2) :
    G.Adj a b := by
  by_contra hab
  obtain ⟨x, _, _, hxa, hxb, hpax⟩ :=
    nonadjacent_leaf_neighbor_low_pair hpart hdeg hlow hg hL2 hLn
      (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2 hb1 hLa hRb hab
  obtain ⟨y, _, hy3, _, hya, hpby⟩ :=
    nonadjacent_leaf_neighbor_low_pair hpart.symm hdeg hlow hg hR2 hRn
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2 ha1 hRb hLa
      (fun hba => hab hba.symm)
  obtain ⟨m, hm2, hbm, hym⟩ := hpby
  exact cross_low_neighbors_disjoint hpart hg (Finset.mem_filter.mp ha).1
    (Finset.mem_filter.mp ha).2 hxa.symm hpax hy3 (Finset.mem_filter.mp hb).2
    hya.symm hxb hm2 hym hbm

private theorem typeA_other_high_degree_two (S : Finset V)
    (hp : highProfile G S) (hA : highTypeA G S)
    {a : V} (ha : a ∈ S) (ha1 : highDegree G a = 1) :
    ∀ x ∈ S, x ≠ a → highDegree G x = 2 := by
  have hone := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hA
  have hthree := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hA
  change (S.filter fun x => highDegree G x = 1).card = 1 at hone
  change (S.filter fun x => highDegree G x = 3).card = 0 at hthree
  intro x hx hxa
  have hxnot1 : highDegree G x ≠ 1 := by
    intro hx1
    exact hxa (Finset.card_le_one.mp hone.le x
      (Finset.mem_filter.mpr ⟨hx, hx1⟩) a (Finset.mem_filter.mpr ⟨ha, ha1⟩))
  have hxnot3 : highDegree G x ≠ 3 := by
    intro hx3
    have hm : x ∈ S.filter (fun x => highDegree G x = 3) :=
      Finset.mem_filter.mpr ⟨hx, hx3⟩
    rw [Finset.card_eq_zero.mp hthree] at hm
    exact Finset.notMem_empty x hm
  have hb := hp.2.2 x hx
  omega

/-- For the actual eleven-by-eleven branch, the existing local profile theorem
supplies nonnegative deficits and excludes high degree zero. Type A on both
actual high-point sets then forces their high leaves to be adjacent. -/
private theorem actual_typeA_leaves_adjacent
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLA : highTypeA G (degreeThree G L))
    (hRA : highTypeA G (degreeThree G R))
    {a b : V} (ha : a ∈ degreeThree G L) (hb : b ∈ degreeThree G R)
    (ha1 : highDegree G a = 1) (hb1 : highDegree G b = 1) :
    G.Adj a b := by
  obtain ⟨_, _, hLp, hRp, hLn, hRn, _⟩ :=
    symmetric_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  exact actual_unique_high_leaves_adjacent hpart hdeg hlow hg hL2 hR2 hLn hRn
    ha hb ha1 hb1
    (typeA_other_high_degree_two _ hLp hLA ha ha1)
    (typeA_other_high_degree_two _ hRp hRA hb hb1)

#check actual_unique_high_leaves_adjacent
#print axioms actual_unique_high_leaves_adjacent
#check actual_typeA_leaves_adjacent
#print axioms actual_typeA_leaves_adjacent

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAAdjacent
