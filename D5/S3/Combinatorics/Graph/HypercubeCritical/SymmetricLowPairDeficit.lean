/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPairDeficit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPairDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Distinct actual highs sharing a low have disjoint relevant low-neighbor capacities. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
import Batteries.Tactic.OpenPrivate

/-! Actual low-neighbor capacity of the high neighborhoods of a lowPair.
For endpoints in L the capacity is the number of low vertices in L. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPairDeficit

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private lowPair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private one_three_cross_impossible three_walk_endpoint_injective neighbor_parts_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private highDegree highDeficit high_degree_le_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem high_low_ne {a b : V} (ha : G.degree a = 3)
    (hb : G.degree b = 2) : a ≠ b := by
  intro he
  rw [he, hb] at ha
  omega

private theorem cross_low_neighbors_disjoint
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {u v y z m : V} (huL : u ∈ L) (hu3 : G.degree u = 3)
    (huv : u ≠ v) (hp : lowPair G u v)
    (hy3 : G.degree y = 3) (hz3 : G.degree z = 3) (huy : G.Adj u y) (hvz : G.Adj v z)
    (hm2 : G.degree m = 2) (hym : G.Adj y m) (hzm : G.Adj z m) : False := by
  obtain ⟨ell, hell2, huell, hvell⟩ := hp
  have hyz : y ≠ z := by
    intro he
    subst z
    exact one_three_cross_impossible hpart hg huL huL huy huell hvell.symm hvz
      huv (high_low_ne hy3 hell2).symm ⟨rfl, rfl⟩
  have he := three_walk_endpoint_injective hpart hg huL huL
    huy hym hzm.symm huell hvell.symm hvz
    (high_low_ne hu3 hm2) hyz huv (high_low_ne hz3 hell2).symm
    ⟨rfl, rfl⟩
  exact high_low_ne hy3 hell2 he.2.1

private theorem low_capacity_deficit_identity (x : V) :
    ((∑ y ∈ degreeThree G (G.neighborFinset x),
      (3 - highDegree G y) : ℕ) : ℤ) =
        2 * (highDegree G x : ℤ) - 2 + highDeficit G x := by
  calc
    _ = ∑ y ∈ degreeThree G (G.neighborFinset x),
        ((3 : ℤ) - (highDegree G y : ℤ)) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro y hy
      exact Nat.cast_sub (high_degree_le_three (Finset.mem_filter.mp hy).2)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Nat.cast_sum, highDeficit]
      change (highDegree G x : ℤ) * 3 -
        ((∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y : ℕ) : ℤ) = _
      ring

private theorem actual_low_pair_capacity
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {u v : V} (huL : u ∈ L) (hvL : v ∈ L)
    (hu3 : G.degree u = 3) (hv3 : G.degree v = 3)
    (huv : u ≠ v) (hp : lowPair G u v) :
    (∑ y ∈ degreeThree G (G.neighborFinset u), (3 - highDegree G y)) +
      (∑ y ∈ degreeThree G (G.neighborFinset v), (3 - highDegree G y)) ≤
        (degreeTwo G L).card ∧
      2 * ((highDegree G u : ℤ) + (highDegree G v : ℤ)) +
        highDeficit G u + highDeficit G v ≤ (degreeTwo G L).card + 4 ∧
      ((degreeTwo G L).card = 4 →
        (∑ y ∈ degreeThree G (G.neighborFinset u), (3 - highDegree G y)) +
          (∑ y ∈ degreeThree G (G.neighborFinset v), (3 - highDegree G y)) ≤ 4 ∧
        2 * ((highDegree G u : ℤ) + (highDegree G v : ℤ)) +
          highDeficit G u + highDeficit G v ≤ 8 ∧
        (highDegree G u = 2 → highDegree G v = 2 →
          0 ≤ highDeficit G u → 0 ≤ highDeficit G v →
            highDeficit G u = 0 ∧ highDeficit G v = 0)) := by
  let A := degreeThree G (G.neighborFinset u)
  let B := degreeThree G (G.neighborFinset v)
  let I := A ∪ B
  have hmem {r y : V} (hy : y ∈ degreeThree G (G.neighborFinset r)) :
      G.Adj r y ∧ G.degree y = 3 := by
    simpa only [degreeThree, Finset.mem_filter, SimpleGraph.mem_neighborFinset] using hy
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    obtain ⟨ell, hell2, huell, hvell⟩ := hp
    exact one_three_cross_impossible hpart hg huL huL (hmem hy).1
      huell hvell.symm (hmem hz).1 huv (high_low_ne (hmem hy).2 hell2).symm
      ⟨rfl, rfl⟩
  have hpairwise : (I : Set V).PairwiseDisjoint
      (fun y => degreeTwo G (G.neighborFinset y)) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro m hm hn
    have hym : G.Adj y m := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hm).1
    have hzm : G.Adj z m := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hn).1
    have hm2 := (Finset.mem_filter.mp hm).2
    have hsame {r : V} (hrL : r ∈ L) (hr3 : G.degree r = 3)
        (hry : G.Adj r y) (hrz : G.Adj r z) : False :=
      one_three_cross_impossible hpart hg hrL hrL hrz hry hym hzm.symm
        (high_low_ne hr3 hm2) hyz ⟨rfl, rfl⟩
    rcases Finset.mem_union.mp hy with hy | hy <;>
      rcases Finset.mem_union.mp hz with hz | hz
    · exact hsame huL hu3 (hmem hy).1 (hmem hz).1
    · exact cross_low_neighbors_disjoint hpart hg huL hu3 huv hp
        (hmem hy).2 (hmem hz).2 (hmem hy).1 (hmem hz).1 hm2 hym hzm
    · have hp' : lowPair G v u := by
        obtain ⟨ell, he2, hue, hve⟩ := hp
        exact ⟨ell, he2, hve, hue⟩
      exact cross_low_neighbors_disjoint hpart hg hvL hv3 huv.symm hp'
        (hmem hy).2 (hmem hz).2 (hmem hy).1 (hmem hz).1 hm2 hym hzm
    · exact hsame hvL hv3 (hmem hy).1 (hmem hz).1
  have hsub : I.biUnion (fun y => degreeTwo G (G.neighborFinset y)) ⊆ degreeTwo G L := by
    intro m hm
    obtain ⟨y, hy, hm⟩ := Finset.mem_biUnion.mp hm
    have hyR : y ∈ R := by
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hpart.mem_of_mem_adj huL (hmem hy).1
      · exact hpart.mem_of_mem_adj hvL (hmem hy).1
    exact Finset.mem_filter.mpr ⟨hpart.symm.mem_of_mem_adj hyR
      ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hm).1),
      (Finset.mem_filter.mp hm).2⟩
  have hcount {y : V} (hy3 : G.degree y = 3) :
      (degreeTwo G (G.neighborFinset y)).card = 3 - highDegree G y := by
    have hh := neighbor_parts_card hdeg y
    dsimp only [highDegree]
    omega
  have hcapacity :
      (∑ y ∈ degreeThree G (G.neighborFinset u), (3 - highDegree G y)) +
        (∑ y ∈ degreeThree G (G.neighborFinset v), (3 - highDegree G y)) ≤
          (degreeTwo G L).card := by
    calc
      _ = (∑ y ∈ A, (degreeTwo G (G.neighborFinset y)).card) +
          (∑ y ∈ B, (degreeTwo G (G.neighborFinset y)).card) := by
        congr 1 <;> apply Finset.sum_congr rfl <;> intro y hy <;>
          exact (hcount (hmem hy).2).symm
      _ = ∑ y ∈ I, (degreeTwo G (G.neighborFinset y)).card :=
        (Finset.sum_union hAB).symm
      _ = (I.biUnion (fun y => degreeTwo G (G.neighborFinset y))).card :=
        (Finset.card_biUnion hpairwise).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcapZ :
      ((∑ y ∈ degreeThree G (G.neighborFinset u), (3 - highDegree G y) : ℕ) : ℤ) +
        ((∑ y ∈ degreeThree G (G.neighborFinset v), (3 - highDegree G y) : ℕ) : ℤ) ≤
          ((degreeTwo G L).card : ℤ) := by exact_mod_cast hcapacity
  rw [low_capacity_deficit_identity u, low_capacity_deficit_identity v] at hcapZ
  have hdelta : 2 * ((highDegree G u : ℤ) + (highDegree G v : ℤ)) +
      highDeficit G u + highDeficit G v ≤ (degreeTwo G L).card + 4 := by omega
  refine ⟨hcapacity, hdelta, ?_⟩
  intro hfour
  have hcap4 := hcapacity
  rw [hfour] at hcap4
  have hdelta8 := hdelta
  rw [hfour] at hdelta8
  norm_num at hdelta8
  refine ⟨hcap4, hdelta8, ?_⟩
  intro hu2 hv2 hdu hdv
  rw [hu2, hv2] at hdelta8
  norm_num at hdelta8
  omega

#check actual_low_pair_capacity
#print axioms actual_low_pair_capacity


end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPairDeficit
