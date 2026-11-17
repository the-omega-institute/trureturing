/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: The actual balanced cubic Q9 thin slice remains fifteen vertices when its size bound is eighteen. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ThinSliceGrayReconstruction
import Batteries.Tactic.OpenPrivate

/-! Actual short paths on both sides of a high-high edge exclude the two new thin-slice cases. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open FifteenSliceStructure (IsK33Subdivision)
open private endpoint_eq_of_short_paths three_walk_endpoint_injective threeWalk_isPath oneWalk threeWalk oneWalk_isPath from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private coordinate_slice_degree_cases low_slice_card_eq_q
  coordinate_slice_low_independent balanced_subset paritySide parity_union parity_bipartite
  parts_card sum_degrees_parts twice_low_le_three_high from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

private def twoWalk {V : Type*} {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) : G.Walk a c :=
  Walk.cons hab (Walk.cons hbc Walk.nil)

private theorem two_walk_isPath
    {V : Type*} {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {a b c : V} (ha : a ∈ L) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : a ≠ c) :
    (twoWalk hab hbc).IsPath := by
  have hb : b ∈ (R : Set V) := hpart.mem_of_mem_adj (show a ∈ (L : Set V) from ha) hab
  have hc : c ∈ (L : Set V) := hpart.mem_of_mem_adj'
    (show b ∈ (R : Set V) from hb) hbc.symm
  have hne : a ≠ b := G.ne_of_adj hab
  have hne' : b ≠ c := G.ne_of_adj hbc
  simp [twoWalk, Walk.cons_isPath_iff, hne, hne', hac]

private def armData {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset (Σ a : V, Σ s : V, V) :=
  (G.neighborFinset r).erase c |>.sigma (fun a =>
    (G.neighborFinset a).erase r |>.sigma (fun s =>
      (G.neighborFinset s).erase a))

private def armMiddleData {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset (Σ a : V, V) :=
  (G.neighborFinset r).erase c |>.sigma (fun a =>
    (G.neighborFinset a).erase r)

private def armMiddleSecond {V : Type*} (q : Σ a : V, V) : V := q.2

private def armEndpoint {V : Type*} (q : Σ a : V, Σ s : V, V) : V := q.2.2

private theorem armMiddleData_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) (hr : G.degree r = 3)
    (hrc : G.Adj r c) (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    2 ≤ (armMiddleData G r c).card := by
  have hcard_r : (G.neighborFinset r).card = 3 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hr
  have hrc_mem : c ∈ G.neighborFinset r := (G.mem_neighborFinset r c).mpr hrc
  have hfirst : ((G.neighborFinset r).erase c).card = 2 := by
    rw [Finset.card_erase_of_mem hrc_mem, hcard_r]
  have hper (a : V) (ha : a ∈ (G.neighborFinset r).erase c) :
      1 ≤ ((G.neighborFinset a).erase r).card := by
    have har : G.Adj r a := (G.mem_neighborFinset r a).mp
      ((Finset.mem_erase.mp ha).2)
    rcases hdeg a with ha2 | ha3
    · rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a r).mpr har.symm),
        SimpleGraph.card_neighborFinset_eq_degree, ha2]
    · rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a r).mpr har.symm),
        SimpleGraph.card_neighborFinset_eq_degree, ha3]
      norm_num
  have hsum := Finset.sum_le_sum (s := (G.neighborFinset r).erase c) hper
  calc
    2 = ((G.neighborFinset r).erase c).card := by omega
    _ = ∑ _a ∈ (G.neighborFinset r).erase c, 1 := by simp
    _ ≤ ∑ a ∈ (G.neighborFinset r).erase c,
        ((G.neighborFinset a).erase r).card := hsum
    _ = (armMiddleData G r c).card := by simp [armMiddleData, Finset.card_sigma]

private theorem arm_middle_second_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    Set.InjOn (armMiddleSecond (V := V))
      (↑(armMiddleData G r c) : Set (Σ a : V, V)) := by
  intro q hq q' hq' he
  have hq0 : (G.Adj r q.1 ∧ q.1 ≠ c) ∧ G.Adj q.1 q.2 ∧ q.2 ≠ r := by
    simpa [armMiddleData, G.mem_neighborFinset] using hq
  have hq'0 : (G.Adj r q'.1 ∧ q'.1 ≠ c) ∧ G.Adj q'.1 q'.2 ∧ q'.2 ≠ r := by
    simpa [armMiddleData, G.mem_neighborFinset] using hq'
  have hqadj : G.Adj r q.1 ∧ G.Adj q.1 q.2 := ⟨hq0.1.1, hq0.2.1⟩
  have hq'adj : G.Adj r q'.1 ∧ G.Adj q'.1 q'.2 := ⟨hq'0.1.1, hq'0.2.1⟩
  have hqne : r ≠ q.2 := by
    exact hq0.2.2.symm
  have hq'ne : r ≠ q'.2 := by
    exact hq'0.2.2.symm
  have hp := two_walk_isPath hpart hrL hqadj.1 hqadj.2 hqne
  have he' : q'.2 = q.2 := by simpa [armMiddleSecond] using he.symm
  rw [he'] at hq'adj hq'ne
  have hp'2 := two_walk_isPath hpart hrL hq'adj.1 hq'adj.2 hq'ne
  have heq : Walk.cons hqadj.1 (Walk.cons hqadj.2 Walk.nil) =
      Walk.cons hq'adj.1 (Walk.cons hq'adj.2 Walk.nil) :=
    endpoint_eq_of_short_paths hg hp hp'2 (by simp)
  have hs : [r, q.1, q.2] = [r, q'.1, q.2] := by
    simpa [Walk.support] using congrArg Walk.support heq
  have hs' := congrArg List.tail hs
  injection hs' with hfirst _
  exact Sigma.ext hfirst (by simpa [armMiddleSecond] using he)

private def armLevelOne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset V :=
  (G.neighborFinset r).erase c

private def armLevelTwo {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset V :=
  (armMiddleData G r c).image armMiddleSecond

private def armLevelThree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset V :=
  (armData G r c).image armEndpoint

private theorem arm_level_one_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) (hr : G.degree r = 3) (hrc : G.Adj r c) :
    (armLevelOne G r c).card = 2 := by
  have hc : (G.neighborFinset r).card = 3 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hr
  have hm : c ∈ G.neighborFinset r := (G.mem_neighborFinset r c).mpr hrc
  simp [armLevelOne, Finset.card_erase_of_mem hm, hc]

private theorem arm_level_two_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    (armLevelTwo G r c).card = (armMiddleData G r c).card := by
  apply Finset.card_image_of_injOn
  intro q hq q' hq' he
  apply arm_middle_second_injective hpart hg hrL hrc
  · exact hq
  · exact hq'
  · exact he

private theorem arm_endpoint_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    Set.InjOn (armEndpoint (V := V)) (↑(armData G r c) : Set (Σ a : V, Σ s : V, V)) := by
  intro q hq q' hq' he
  have hq0 : (G.Adj r q.1 ∧ q.1 ≠ c) ∧
      ((G.Adj q.1 q.2.1 ∧ q.2.1 ≠ r) ∧
        (G.Adj q.2.1 q.2.2 ∧ q.2.2 ≠ q.1)) := by
    simpa [armData, G.mem_neighborFinset] using hq
  have hq'0 : (G.Adj r q'.1 ∧ q'.1 ≠ c) ∧
      ((G.Adj q'.1 q'.2.1 ∧ q'.2.1 ≠ r) ∧
        (G.Adj q'.2.1 q'.2.2 ∧ q'.2.2 ≠ q'.1)) := by
    simpa [armData, G.mem_neighborFinset] using hq'
  have hqne : r ≠ q.2.1 := hq0.2.1.2.symm
  have hq'ne : r ≠ q'.2.1 := hq'0.2.1.2.symm
  have hqend : q.1 ≠ q.2.2 := hq0.2.2.2.symm
  have hq'end : q'.1 ≠ q'.2.2 := hq'0.2.2.2.symm
  have hwalk := three_walk_endpoint_injective hpart hg hrL hrL
    hq0.1.1 hq0.2.1.1 hq0.2.2.1
    hq'0.1.1 hq'0.2.1.1 hq'0.2.2.1 hqne hqend hq'ne hq'end
    (by simpa [armEndpoint] using he)
  obtain ⟨_, hfirst, hsecond, hend⟩ := hwalk
  have hsnd : q.2 = q'.2 := by
    apply Sigma.ext hsecond
    exact hend.heq
  apply Sigma.ext hfirst
  exact hsnd.heq

private theorem arm_level_three_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    (armLevelThree G r c).card = (armData G r c).card := by
  apply Finset.card_image_of_injOn
  intro q hq q' hq' he
  apply arm_endpoint_injective hpart hg hrL hrc
  · exact hq
  · exact hq'
  · exact he

private theorem arm_level_one_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r c x : V} (hx : x ∈ armLevelOne G r c) :
    x ≠ c ∧ G.Adj r x := by
  simpa [armLevelOne, G.mem_neighborFinset] using hx

private theorem arm_level_two_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r c x : V} (hx : x ∈ armLevelTwo G r c) :
    ∃ a, a ∈ (G.neighborFinset r).erase c ∧ x ∈ (G.neighborFinset a).erase r := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  have hq0 := Finset.mem_sigma.mp hq
  exact ⟨q.1, hq0.1, hq0.2⟩

private theorem arm_level_three_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r c x : V} (hx : x ∈ armLevelThree G r c) :
    ∃ a s, a ∈ (G.neighborFinset r).erase c ∧
      s ∈ (G.neighborFinset a).erase r ∧ x ∈ (G.neighborFinset s).erase a := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  have hq' : (G.Adj r q.1 ∧ q.1 ≠ c) ∧
      ((G.Adj q.1 q.2.1 ∧ q.2.1 ≠ r) ∧
        (G.Adj q.2.1 q.2.2 ∧ q.2.2 ≠ q.1)) := by
    simpa [armData, G.mem_neighborFinset, and_comm] using hq
  exact ⟨q.1, q.2.1, by simpa [and_comm] using hq'.1,
    by simpa [and_comm] using hq'.2.1,
    by simpa [armEndpoint, and_comm] using hq'.2.2⟩

private theorem no_same_end_different_length
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {r z : V}
    (hg : (8 : ℕ∞) ≤ G.egirth) {p q : G.Walk r z} (hp : p.IsPath) (hq : q.IsPath)
    (hne : p.length ≠ q.length) (hlen : p.length + q.length ≤ 6) : False := by
  apply hne
  congr 1
  exact endpoint_eq_of_short_paths (G := G) hg hp hq hlen

private theorem arm_levels_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    Disjoint ({r} : Finset V) (armLevelOne G r c) ∧
    Disjoint ({r} : Finset V) (armLevelTwo G r c) ∧
    Disjoint ({r} : Finset V) (armLevelThree G r c) ∧
    Disjoint (armLevelOne G r c) (armLevelTwo G r c) ∧
    Disjoint (armLevelOne G r c) (armLevelThree G r c) ∧
    Disjoint (armLevelTwo G r c) (armLevelThree G r c) := by
  have hroot1 : Disjoint ({r} : Finset V) (armLevelOne G r c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    have hx' := arm_level_one_spec hxr
    have hxr' : x = r := Finset.mem_singleton.mp hx
    exact (G.ne_of_adj hx'.2) hxr'.symm
  have hroot2 : Disjoint ({r} : Finset V) (armLevelTwo G r c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    obtain ⟨a, _, hs⟩ := arm_level_two_spec hxr
    exact (Finset.mem_erase.mp hs).1 (by simpa using hx)
  have hroot3 : Disjoint ({r} : Finset V) (armLevelThree G r c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    obtain ⟨a, s, ha, hs, he⟩ := arm_level_three_spec hxr
    have haR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL)
      ((G.mem_neighborFinset r a).mp (Finset.mem_erase.mp ha).2)
    have hsL := hpart.mem_of_mem_adj' haR
      ((G.mem_neighborFinset a s).mp (Finset.mem_erase.mp hs).2).symm
    have hxR := hpart.mem_of_mem_adj hsL
      ((G.mem_neighborFinset s x).mp (Finset.mem_erase.mp he).2)
    have hxL : x ∈ (L : Set V) := (Finset.mem_singleton.mp hx).symm ▸ hrL
    exact Set.disjoint_left.mp hpart.disjoint hxL hxR
  have h12 : Disjoint (armLevelOne G r c) (armLevelTwo G r c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hs⟩ := arm_level_two_spec hy
    obtain ⟨hc, hax⟩ := arm_level_one_spec hx
    have hp : (oneWalk hax).IsPath := by simp [oneWalk, G.ne_of_adj hax]
    have hac : r ≠ x := G.ne_of_adj hax
    have hq : (twoWalk ((G.mem_neighborFinset r a).mp (Finset.mem_erase.mp ha).2)
        ((G.mem_neighborFinset a x).mp (Finset.mem_erase.mp hs).2)).IsPath :=
      two_walk_isPath hpart hrL ((G.mem_neighborFinset r a).mp (Finset.mem_erase.mp ha).2)
        ((G.mem_neighborFinset a x).mp (Finset.mem_erase.mp hs).2) (Finset.mem_erase.mp hs).1.symm
    exact no_same_end_different_length hg hp hq (by simp [oneWalk, twoWalk]) (by simp [oneWalk, twoWalk])
  have h13 : Disjoint (armLevelOne G r c) (armLevelThree G r c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, s, ha, hs, he⟩ := arm_level_three_spec hy
    obtain ⟨hc, hax⟩ := arm_level_one_spec hx
    have hp : (oneWalk hax).IsPath := by simp [oneWalk, G.ne_of_adj hax]
    have hq := threeWalk_isPath hpart hrL
      ((G.mem_neighborFinset r a).mp (Finset.mem_erase.mp ha).2)
      ((G.mem_neighborFinset a s).mp (Finset.mem_erase.mp hs).2)
      ((G.mem_neighborFinset s x).mp (Finset.mem_erase.mp he).2)
      (Finset.mem_erase.mp hs).1.symm (Finset.mem_erase.mp he).1.symm
    exact no_same_end_different_length hg hp hq (by simp [oneWalk, threeWalk])
      (by simp [oneWalk, threeWalk])
  have h23 : Disjoint (armLevelTwo G r c) (armLevelThree G r c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, s, ha, hs, he⟩ := arm_level_three_spec hy
    obtain ⟨a', ha', hs'⟩ := arm_level_two_spec hx
    have hp := two_walk_isPath hpart hrL
      ((G.mem_neighborFinset r a').mp (Finset.mem_erase.mp ha').2)
      ((G.mem_neighborFinset a' x).mp (Finset.mem_erase.mp hs').2) (Finset.mem_erase.mp hs').1.symm
    have hq := threeWalk_isPath hpart hrL
      ((G.mem_neighborFinset r a).mp (Finset.mem_erase.mp ha).2)
      ((G.mem_neighborFinset a s).mp (Finset.mem_erase.mp hs).2)
      ((G.mem_neighborFinset s x).mp (Finset.mem_erase.mp he).2)
      (Finset.mem_erase.mp hs).1.symm (Finset.mem_erase.mp he).1.symm
    exact no_same_end_different_length hg hp hq (by simp [twoWalk, threeWalk])
      (by simp [twoWalk, threeWalk])
  exact ⟨hroot1, hroot2, hroot3, h12, h13, h23⟩


private theorem armData_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V)
    (hr : G.degree r = 3) (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hrc : G.Adj r c) :
    4 ≤ (armData G r c).card := by
  have hcard_r : (G.neighborFinset r).card = 3 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hr
  have hrc_mem : c ∈ G.neighborFinset r := (G.mem_neighborFinset r c).mpr hrc
  have hfirst : ((G.neighborFinset r).erase c).card = 2 := by
    rw [Finset.card_erase_of_mem hrc_mem, hcard_r]
  have hper (a : V) (ha : a ∈ (G.neighborFinset r).erase c) :
      2 ≤ ∑ s ∈ (G.neighborFinset a).erase r,
        ((G.neighborFinset s).erase a).card := by
    have har : G.Adj r a := (G.mem_neighborFinset r a).mp
      ((Finset.mem_erase.mp ha).2)
    rcases hdeg a with ha2 | ha3
    · have hlow_ne : ∀ s ∈ (G.neighborFinset a).erase r, G.degree s = 3 := by
        intro s hs
        have hsa : G.Adj a s := (G.mem_neighborFinset a s).mp
          ((Finset.mem_erase.mp hs).2)
        rcases hdeg s with hs2 | hs3
        · exact (hlow hsa ha2 hs2).elim
        · exact hs3
      have hneigh : ((G.neighborFinset a).erase r).card = 1 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a r).mpr har.symm)]
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using ha2
      have hsum : ∑ s ∈ (G.neighborFinset a).erase r,
          ((G.neighborFinset s).erase a).card ≥
          ∑ _s ∈ (G.neighborFinset a).erase r, 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hs3 := hlow_ne s hs
        have hsa : G.Adj a s := (G.mem_neighborFinset a s).mp
          ((Finset.mem_erase.mp hs).2)
        have hcard_s : (G.neighborFinset s).card = 3 := by
          simpa [SimpleGraph.card_neighborFinset_eq_degree] using hs3
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset s a).mpr hsa.symm), hcard_s]
      simpa [hneigh] using hsum
    · have hneigh : ((G.neighborFinset a).erase r).card = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a r).mpr har.symm)]
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using ha3
      have hsum : ∑ s ∈ (G.neighborFinset a).erase r,
          ((G.neighborFinset s).erase a).card ≥
          ∑ _s ∈ (G.neighborFinset a).erase r, 1 := by
        apply Finset.sum_le_sum
        intro s hs
        have hsa : G.Adj a s := (G.mem_neighborFinset a s).mp
          ((Finset.mem_erase.mp hs).2)
        rcases hdeg s with hs2 | hs3
        · rw [Finset.card_erase_of_mem ((G.mem_neighborFinset s a).mpr hsa.symm),
            show (G.neighborFinset s).card = 2 by
              simpa [SimpleGraph.card_neighborFinset_eq_degree] using hs2]
        · rw [Finset.card_erase_of_mem ((G.mem_neighborFinset s a).mpr hsa.symm),
            show (G.neighborFinset s).card = 3 by
              simpa [SimpleGraph.card_neighborFinset_eq_degree] using hs3]
          omega
      simpa [hneigh] using hsum
  have hsum := Finset.sum_le_sum (s := (G.neighborFinset r).erase c) hper
  calc
    4 = 2 * ((G.neighborFinset r).erase c).card := by omega
    _ = ∑ _a ∈ (G.neighborFinset r).erase c, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ (G.neighborFinset r).erase c,
        ∑ s ∈ (G.neighborFinset a).erase r,
          ((G.neighborFinset s).erase a).card := hsum
    _ = (armData G r c).card := by
      simp [armData, Finset.card_sigma]

private def sideTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset V :=
  {r} ∪ armLevelOne G r c ∪ armLevelTwo G r c ∪ armLevelThree G r c

private theorem sideTree_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L)
    (hrc : G.Adj r c) (hr : G.degree r = 3) :
    (sideTree G r c).card = 3 + (armMiddleData G r c).card + (armData G r c).card := by
  obtain ⟨h01,h02,h03,h12,h13,h23⟩ := arm_levels_disjoint hpart hg hrL hrc
  simp only [sideTree, Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h03,h13⟩,h23⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02,h12⟩),
    Finset.card_union_of_disjoint h01, Finset.card_singleton,
    arm_level_one_card G r c hr hrc, arm_level_two_card hpart hg hrL hrc,
    arm_level_three_card hpart hg hrL hrc]

private theorem short_paths_unique_seven
    {V : Type*} {G : SimpleGraph V} (hg : (8 : ℕ∞) ≤ G.egirth)
    {u w : V} {p q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length ≤ 7) : p = q := by
  by_contra hn
  obtain ⟨z, _, _, cyc, hc, hlen'⟩ := hp.exists_isCycle_length_le_add_of_ne hq hn
  have h8 : 8 ≤ cyc.length := ENat.natCast_le_natCast.mp (hg.trans hc.egirth_le_length)
  omega

private theorem sideTree_path
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c x : V} (hrL : r ∈ L) (hrc : G.Adj r c)
    (hx : x ∈ sideTree G r c) :
    ∃ p : G.Walk r x, p.IsPath ∧ p.length ≤ 3 ∧ c ∉ p.support := by
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hrcne := G.ne_of_adj hrc
  have htwo_avoid {a s : V} (ha : a ∈ (G.neighborFinset r).erase c)
      (hs : s ∈ (G.neighborFinset a).erase r) : s ≠ c := by
    have haR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL)
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2)
    have hsL := hpart.mem_of_mem_adj' haR
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2).symm
    intro h; subst s
    exact Set.disjoint_left.mp hpart.disjoint hsL hcR
  simp only [sideTree, Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with ((rfl | hx) | hx) | hx
  · exact ⟨Walk.nil, by simp, by simp, by simpa using hrcne.symm⟩
  · obtain ⟨hn, ha⟩ := arm_level_one_spec hx
    exact ⟨oneWalk ha, oneWalk_isPath ha, by simp [oneWalk], by
      simp [oneWalk, hrcne.symm, hn.symm]⟩
  · obtain ⟨a, ha, hs⟩ := arm_level_two_spec hx
    let p := twoWalk ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2)
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2)
    refine ⟨p, two_walk_isPath hpart hrL _ _ (Finset.mem_erase.mp hs).1.symm,
      by simp [p,twoWalk], ?_⟩
    simp [p,twoWalk,hrcne.symm,(Finset.mem_erase.mp ha).1.symm,(htwo_avoid ha hs).symm]
  · obtain ⟨a, s, ha, hs, he⟩ := arm_level_three_spec hx
    let p := threeWalk ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2)
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2)
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp he).2)
    have hp : p.IsPath := threeWalk_isPath hpart hrL _ _ _
      (Finset.mem_erase.mp hs).1.symm (Finset.mem_erase.mp he).1.symm
    have hxc : x ≠ c := by
      intro h; subst x
      have heq := endpoint_eq_of_short_paths hg hp (oneWalk_isPath hrc)
        (by simp [p,threeWalk,oneWalk])
      have hlen := congrArg Walk.length heq
      simp [p,threeWalk,oneWalk] at hlen
    refine ⟨p,hp,by simp [p,threeWalk],?_⟩
    simp [p,threeWalk,hrcne.symm,(Finset.mem_erase.mp ha).1.symm,
      (htwo_avoid ha hs).symm,hxc.symm]

private theorem sideTrees_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    Disjoint (sideTree G r c) (sideTree G c r) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  obtain ⟨p,hp,hlp,hcp⟩ := sideTree_path hpart hg hrL hrc hx
  obtain ⟨q,hq,hlq,hrq⟩ := sideTree_path hpart.symm hg hcR hrc.symm hy
  have hcq : (Walk.cons hrc q).IsPath := hq.cons hrq
  have he := short_paths_unique_seven hg hp hcq (by simp only [Walk.length_cons]; omega)
  apply hcp
  rw [he]
  simp only [Walk.support_cons,List.mem_cons]
  exact Or.inr q.start_mem_support

private theorem double_root_count
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c)
    (hr : G.degree r = 3) (hc : G.degree c = 3) :
    18 ≤ Fintype.card V ∧
      (Fintype.card V ≤ 18 → (armMiddleData G r c).card = 2 ∧
        (armMiddleData G c r).card = 2 ∧ sideTree G r c ∪ sideTree G c r = Finset.univ) := by
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hdis := sideTrees_disjoint hpart hg hrL hrc
  have hcard1 := sideTree_card hpart hg hrL hrc hr
  have hcard2 := sideTree_card hpart.symm hg hcR hrc.symm hc
  have hm1 := armMiddleData_card_lower G r c hr hrc hdeg
  have hm2 := armMiddleData_card_lower G c r hc hrc.symm hdeg
  have he1 := armData_card_lower G r c hr hdeg hlow hrc
  have he2 := armData_card_lower G c r hc hdeg hlow hrc.symm
  have hcard := Finset.card_le_card (Finset.subset_univ (sideTree G r c ∪ sideTree G c r))
  rw [Finset.card_union_of_disjoint hdis,Finset.card_univ] at hcard
  refine ⟨by omega, fun hN => ⟨by omega,by omega,?_⟩⟩
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ,Finset.card_union_of_disjoint hdis]
  omega

private theorem first_low_of_middle_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r c : V} (hr : G.degree r = 3) (hrc : G.Adj r c)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hm : (armMiddleData G r c).card = 2) :
    ∀ a ∈ armLevelOne G r c, G.degree a = 2 := by
  have hcard := arm_level_one_card G r c hr hrc
  have hcard' : ((G.neighborFinset r).erase c).card = 2 := hcard
  have hbound (a : V) (ha : a ∈ armLevelOne G r c) :
      1 ≤ ((G.neighborFinset a).erase r).card := by
    have hadj := (arm_level_one_spec ha).2
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj.symm),
      SimpleGraph.card_neighborFinset_eq_degree]
    rcases hdeg a with h | h <;> omega
  intro a ha
  rcases hdeg a with h | h
  · exact h
  · have hlt : 1 < ((G.neighborFinset a).erase r).card := by
      have hadj := (arm_level_one_spec ha).2
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj.symm),
        SimpleGraph.card_neighborFinset_eq_degree,h]
      norm_num
    have hsum := Finset.sum_lt_sum hbound ⟨a,ha,hlt⟩
    have hsum' : 2 < (armMiddleData G r c).card := by
      simpa [armMiddleData,armLevelOne,Finset.card_sigma,hcard'] using hsum
    omega

private def highWithHigh {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  (degreeThree G Finset.univ).filter fun v => ∃ w, G.Adj v w ∧ G.degree w = 3

private theorem high_neighbor_deficit
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) :
    2 * (degreeTwo G Finset.univ).card + (highWithHigh G).card ≤
      3 * (degreeThree G Finset.univ).card := by
  let lo := degreeTwo G Finset.univ
  let hi := degreeThree G Finset.univ
  have hl (v : V) (hv : v ∈ lo) : hi.bipartiteAbove G.Adj v = G.neighborFinset v := by
    ext w
    simp only [Finset.mem_bipartiteAbove,SimpleGraph.mem_neighborFinset]
    constructor
    · exact And.right
    · intro hvw
      have hw3 : G.degree w = 3 := by
        rcases hdeg w with hw | hw
        · exact (hlow hvw (Finset.mem_filter.mp hv).2 hw).elim
        · exact hw
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw3⟩,hvw⟩
  have hc : (∑ w ∈ hi, (lo.bipartiteBelow G.Adj w).card) = 2 * lo.card := by
    rw [← Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc
      _ = ∑ _v ∈ lo, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hl v hv,SimpleGraph.card_neighborFinset_eq_degree]
        exact (Finset.mem_filter.mp hv).2
      _ = _ := by simp [Nat.mul_comm]
  have hbound (w : V) (hw : w ∈ hi) :
      (lo.bipartiteBelow G.Adj w).card +
        (if ∃ z, G.Adj w z ∧ G.degree z = 3 then 1 else 0) ≤ 3 := by
    have hw3 := (Finset.mem_filter.mp hw).2
    have hsub : lo.bipartiteBelow G.Adj w ⊆ G.neighborFinset w := by
      intro v hv
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hv).2.symm
    split_ifs with hb
    · obtain ⟨z,hz,hz3⟩ := hb
      have hznot : z ∉ lo.bipartiteBelow G.Adj w := by
        intro hzmem
        have hz2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hzmem).1).2
        omega
      have hs : insert z (lo.bipartiteBelow G.Adj w) ⊆ G.neighborFinset w :=
        Finset.insert_subset_iff.mpr ⟨(G.mem_neighborFinset _ _).mpr hz,hsub⟩
      have hh := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem hznot,SimpleGraph.card_neighborFinset_eq_degree,hw3] at hh
      omega
    · have hh := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree,hw3] at hh
      omega
  have hs := Finset.sum_le_sum (s := hi) hbound
  simpa [Finset.sum_add_distrib,hc,highWithHigh,hi,lo,Nat.mul_comm,
    Finset.sum_boole] using hs

private def roots {V : Type*} [DecidableEq V] (r c : V) : Finset V := {r,c}

private def middles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset V := armLevelTwo G r c ∪ armLevelTwo G c r

private def leaves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r c : V) : Finset V := armLevelThree G r c ∪ armLevelThree G c r

private theorem global_layers_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c) :
    Disjoint (roots r c) (middles G r c) ∧
    Disjoint (roots r c ∪ middles G r c) (leaves G r c) := by
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have h1 := arm_levels_disjoint hpart hg hrL hrc
  have h2 := arm_levels_disjoint hpart.symm hg hcR hrc.symm
  have hd := sideTrees_disjoint hpart hg hrL hrc
  simp only [sideTree,Finset.disjoint_union_left,Finset.disjoint_union_right] at hd
  simp only [roots,middles,leaves,show ({r,c} : Finset V) = {r} ∪ {c} by simp,
    Finset.disjoint_union_left,Finset.disjoint_union_right]
  aesop (add safe Disjoint.symm)

private theorem ten_low_eighteen_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c)
    (hr : G.degree r = 3) (hc : G.degree c = 3)
    (hN : Fintype.card V = 18) (hq : (degreeTwo G Finset.univ).card = 10) : False := by
  obtain ⟨_,heq⟩ := double_root_count hpart hg hdeg hlow hrL hrc hr hc
  obtain ⟨hm1,hm2,hcover⟩ := heq (by omega)
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hl1 := first_low_of_middle_two hr hrc hdeg hm1
  have hl2 := first_low_of_middle_two hc hrc.symm hdeg hm2
  have hp := parts_card G hdeg Finset.univ
  have hhigh : (degreeThree G Finset.univ).card = 8 := by
    rw [Finset.card_univ] at hp
    omega
  have hbad : (highWithHigh G).card ≤ 4 := by
    have hh := high_neighbor_deficit G hdeg hlow
    omega
  have hmcard : (middles G r c).card ≤ 4 := by
    have hh := Finset.card_union_le (armLevelTwo G r c) (armLevelTwo G c r)
    rw [arm_level_two_card hpart hg hrL hrc,
      arm_level_two_card hpart.symm hg hcR hrc.symm] at hh
    change (armLevelTwo G r c ∪ armLevelTwo G c r).card ≤ 4
    omega
  have hrccard : (roots r c).card = 2 := by simp [roots,G.ne_of_adj hrc]
  have hhighcover : degreeThree G Finset.univ ⊆
      roots r c ∪ middles G r c ∪ degreeThree G (leaves G r c) := by
    intro x hx
    have hx3 := (Finset.mem_filter.mp hx).2
    have hxU : x ∈ sideTree G r c ∪ sideTree G c r := by rw [hcover]; exact Finset.mem_univ _
    simp only [sideTree,Finset.mem_union,Finset.mem_singleton] at hxU
    simp only [roots,middles,leaves,degreeThree,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.mem_filter]
    rcases hxU with (((h | h) | h) | h) | (((h | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · have hh := hl1 x h; omega
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr ⟨Or.inl h,hx3⟩
    · exact Or.inl (Or.inl (Or.inr h))
    · have hh := hl2 x h; omega
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr ⟨Or.inr h,hx3⟩
  have hleafcard : 2 ≤ (degreeThree G (leaves G r c)).card := by
    have h := Finset.card_le_card hhighcover
    have hh := Finset.card_union_le (roots r c ∪ middles G r c) (degreeThree G (leaves G r c))
    have hh' := Finset.card_union_le (roots r c) (middles G r c)
    omega
  have hparent (x : V) (hx : x ∈ degreeThree G (leaves G r c)) :
      ∃ s, s ∈ middles G r c ∧ G.degree s = 3 ∧ G.Adj s x := by
    have hx' := (Finset.mem_filter.mp hx).1
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · obtain ⟨a,s,ha,hs,he⟩ := arm_level_three_spec hx'
      have ha2 := hl1 a ha
      have hs3 : G.degree s = 3 := by
        rcases hdeg s with h | h
        · exact (hlow ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2) ha2 h).elim
        · exact h
      refine ⟨s,Finset.mem_union_left _ ?_,hs3,
        (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp he).2⟩
      exact Finset.mem_image.mpr ⟨⟨a,s⟩,Finset.mem_sigma.mpr ⟨ha,hs⟩,rfl⟩
    · obtain ⟨a,s,ha,hs,he⟩ := arm_level_three_spec hx'
      have ha2 := hl2 a ha
      have hs3 : G.degree s = 3 := by
        rcases hdeg s with h | h
        · exact (hlow ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2) ha2 h).elim
        · exact h
      refine ⟨s,Finset.mem_union_right _ ?_,hs3,
        (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp he).2⟩
      exact Finset.mem_image.mpr ⟨⟨a,s⟩,Finset.mem_sigma.mpr ⟨ha,hs⟩,rfl⟩
  have hrootsbad : roots r c ⊆ highWithHigh G := by
    intro x hx
    simp only [roots,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,c,hrc,hc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,r,hrc.symm,hr⟩
  have hleavesbad : degreeThree G (leaves G r c) ⊆ highWithHigh G := by
    intro x hx
    obtain ⟨s,_,hs3,hsx⟩ := hparent x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩,s,hsx.symm,hs3⟩
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (degreeThree G (leaves G r c)).card)
  obtain ⟨s,hs,hs3,hsx⟩ := hparent x hx
  have hsbad : s ∈ highWithHigh G := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hs3⟩,x,hsx,(Finset.mem_filter.mp hx).2⟩
  obtain ⟨hrm,hrml⟩ := global_layers_disjoint hpart hg hrL hrc
  have hrl : Disjoint (roots r c) (degreeThree G (leaves G r c)) :=
    hrml.mono (Finset.subset_union_left) (Finset.filter_subset _ _)
  have hsnot : s ∉ roots r c ∪ degreeThree G (leaves G r c) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.disjoint_left.mp hrm h hs
    · exact Finset.disjoint_left.mp hrml (Finset.mem_union_right _ hs) (Finset.mem_filter.mp h).1
  have hsub : insert s (roots r c ∪ degreeThree G (leaves G r c)) ⊆ highWithHigh G :=
    Finset.insert_subset_iff.mpr ⟨hsbad,Finset.union_subset hrootsbad hleavesbad⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hsnot,Finset.card_union_of_disjoint hrl,hrccard] at hh
  omega

private theorem high_edge_exists
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hstrict : 2 * (degreeTwo G Finset.univ).card < 3 * (degreeThree G Finset.univ).card) :
    ∃ r c, G.Adj r c ∧ G.degree r = 3 ∧ G.degree c = 3 := by
  by_contra hn
  have hleft (v : V) (hv : v ∈ degreeThree G Finset.univ) :
      (degreeTwo G Finset.univ).bipartiteAbove G.Adj v = G.neighborFinset v := by
    ext w
    simp only [Finset.mem_bipartiteAbove,SimpleGraph.mem_neighborFinset]
    constructor
    · exact And.right
    · intro hvw
      have hw2 : G.degree w = 2 := by
        rcases hdeg w with h | h
        · exact h
        · exact (hn ⟨v,w,hvw,(Finset.mem_filter.mp hv).2,h⟩).elim
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw2⟩,hvw⟩
  have hright (w : V) (hw : w ∈ degreeTwo G Finset.univ) :
      ((degreeThree G Finset.univ).bipartiteBelow G.Adj w).card ≤ 2 := by
    have hs : (degreeThree G Finset.univ).bipartiteBelow G.Adj w ⊆ G.neighborFinset w := by
      intro v hv
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hv).2.symm
    have hh := Finset.card_le_card hs
    rwa [SimpleGraph.card_neighborFinset_eq_degree,(Finset.mem_filter.mp hw).2] at hh
  have hh := Finset.card_mul_le_card_mul (r := G.Adj)
    (s := degreeThree G Finset.univ) (t := degreeTwo G Finset.univ)
    (m := 3) (n := 2) (fun v hv => by
      rw [hleft v hv,SimpleGraph.card_neighborFinset_eq_degree,(Finset.mem_filter.mp hv).2]) hright
  omega

/-- The bound concerns the original coordinate-zero slice of the original
Huang-balanced cubic support; the comparison is a total cube equivalence. -/
theorem eighteen_point_slice_gray_reconstruction {C : Finset (Q 9)} (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card ≤ 18) :
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (BalancedCriticalSpectrum.flip x i) =
        BalancedCriticalSpectrum.flip (g x) (pi i)) ∧
      C = (GrayGridComponent.support 3).image g := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 := fun v =>
    coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False := by
    intro v w hxy hx hy
    exact coordinate_slice_low_independent hr hb hxy hx hy
  have hbal : IsBalanced S := balanced_subset hb (Finset.filter_subset _ _)
  have hg : (8 : ℕ∞) ≤ G.egirth := BalancedCubeGirth.eight_le_egirth S hbal
  have hqcard : (degreeTwo G Finset.univ).card = directionEdges C 0 := low_slice_card_eq_q hr
  have h54 : 54 ≤ C.card := by
    by_contra hn
    exact BalancedCubeFiftyFourLowerBound.result ⟨C,hC,hr,hb,by omega⟩
  have h6 : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hScard : Fintype.card (S : Set (Q 9)) = S.card := by simp
  have hN18 : Fintype.card (S : Set (Q 9)) ≤ 18 := by rw [hScard]; exact hs
  have hp := parts_card G hdeg Finset.univ
  have hi := twice_low_le_three_high G hdeg hlow
  have hsum : 2 * (degreeTwo G Finset.univ).card +
      3 * (degreeThree G Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_parts G hdeg Finset.univ]
    exact G.sum_degrees_eq_twice_card_edges
  rw [Finset.card_univ] at hp
  have hN16 : Fintype.card (S : Set (Q 9)) ≤ 16 := by
    by_contra hn
    have hcases :
        (Fintype.card (S : Set (Q 9)) = 17 ∧ (degreeTwo G Finset.univ).card = 9) ∨
        (Fintype.card (S : Set (Q 9)) = 18 ∧ (degreeTwo G Finset.univ).card = 10) := by omega
    have hstrict : 2 * (degreeTwo G Finset.univ).card <
        3 * (degreeThree G Finset.univ).card := by omega
    obtain ⟨r,c,hrc,hr3,hc3⟩ := high_edge_exists G hdeg hstrict
    have hpart := parity_bipartite S
    have hcover := parity_union S
    have horient : r ∈ paritySide S false ∨ r ∈ paritySide S true := by
      rw [← Finset.mem_union,hcover]
      exact Finset.mem_univ _
    rcases hcases with ⟨hN,hq⟩ | ⟨hN,hq⟩
    · rcases horient with hrL | hrR
      · have hh := (double_root_count hpart hg hdeg hlow hrL hrc hr3 hc3).1
        omega
      · have hh := (double_root_count hpart.symm hg hdeg hlow hrR hrc hr3 hc3).1
        omega
    · rcases horient with hrL | hrR
      · exact ten_low_eighteen_impossible hpart hg hdeg hlow hrL hrc hr3 hc3 hN hq
      · exact ten_low_eighteen_impossible hpart.symm hg hdeg hlow hrR hrc hr3 hc3 hN hq
  have hs16 : (coordinateSlice C b).card ≤ 16 := by
    change S.card ≤ 16
    omega
  obtain ⟨_,hs15,_⟩ := ThinCoordinateSlice.thin_coordinate_slice hC hr hb b hs16
  exact ThinSliceGrayReconstruction.thin_slice_gray_reconstruction hC hr hb b (by omega)

#print axioms eighteen_point_slice_gray_reconstruction

end D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
