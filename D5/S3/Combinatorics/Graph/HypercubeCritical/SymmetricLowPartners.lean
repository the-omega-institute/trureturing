/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: A full-degree-three vertex with two actual high neighbors has one actual low neighbor, whose other endpoint is a uniquely determined distinct high vertex. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
import Batteries.Tactic.OpenPrivate

/-! Actual low neighbors and their uniquely determined high partners. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing

attribute [local instance] Classical.propDecidable

open private neighbor_parts_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private lowPair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem other_high_of_low_neighbor
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {x w : V} (hw : G.degree w = 2) (hxw : G.Adj x w) :
    ∃ y, x ≠ y ∧ G.degree y = 3 ∧ G.Adj y w ∧
      G.neighborFinset w = {x, y} := by
  have hc : 1 < (G.neighborFinset w).card := by
    rw [G.card_neighborFinset_eq_degree, hw]
    norm_num
  obtain ⟨y, hyN, hyx⟩ := Finset.exists_mem_ne hc x
  have hyw : G.Adj y w := ((G.mem_neighborFinset _ _).mp hyN).symm
  have hy3 : G.degree y = 3 := by
    rcases hdeg y with hy | hy
    · exact False.elim (hlow hyw hy hw)
    · exact hy
  refine ⟨y, hyx.symm, hy3, hyw, ?_⟩
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (G.mem_neighborFinset _ _).mpr hxw.symm
    · exact Finset.mem_singleton.mp hz ▸ hyN
  · simp [G.card_neighborFinset_eq_degree, hw, hyx.symm]

private theorem unique_low_partner
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {x : V} (hx : G.degree x = 3)
    (hxhigh : (degreeThree G (G.neighborFinset x)).card = 2) :
    ∃ w y, G.degree w = 2 ∧ G.degree y = 3 ∧ x ≠ y ∧
      G.Adj x w ∧ G.Adj y w ∧ G.neighborFinset w = {x, y} ∧
      (∀ z, x ≠ z → lowPair G x z → z = y) ∧
      (∀ w', G.degree w' = 2 → G.Adj x w' → w' = w) := by
  have hp := neighbor_parts_card hdeg x
  have hc : (degreeTwo G (G.neighborFinset x)).card = 1 := by omega
  obtain ⟨w, hwset⟩ := Finset.card_eq_one.mp hc
  have hwm : w ∈ degreeTwo G (G.neighborFinset x) := by
    rw [hwset]
    exact Finset.mem_singleton_self _
  have hw : G.degree w = 2 := (Finset.mem_filter.mp hwm).2
  have hxw : G.Adj x w := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hwm).1
  obtain ⟨y, hxy, hy3, hyw, hN⟩ := other_high_of_low_neighbor hdeg hlow hw hxw
  have huniq (w' : V) (hw' : G.degree w' = 2) (hxw' : G.Adj x w') : w' = w := by
    have hm : w' ∈ degreeTwo G (G.neighborFinset x) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw', hw'⟩
    simpa only [hwset, Finset.mem_singleton] using hm
  refine ⟨w, y, hw, hy3, hxy, hxw, hyw, hN, ?_, huniq⟩
  intro z hxz hz
  rcases hz with ⟨w', hw', hxw', hzw'⟩
  have he := huniq w' hw' hxw'
  have hzm : z ∈ G.neighborFinset w := (G.mem_neighborFinset _ _).mpr (he ▸ hzw'.symm)
  rw [hN] at hzm
  rcases Finset.mem_insert.mp hzm with hzx | hzy
  · exact False.elim (hxz hzx.symm)
  · exact Finset.mem_singleton.mp hzy

private theorem low_pair_excludes_high_neighbor_degree_three
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    {x y : V} (hx : G.degree x = 3) (hpair : lowPair G x y) :
    (degreeThree G (G.neighborFinset x)).card ≠ 3 := by
  intro hh
  have hp := neighbor_parts_card hdeg x
  have hc : (degreeTwo G (G.neighborFinset x)).card = 0 := by omega
  rcases hpair with ⟨w, hw, hxw, _⟩
  have hm : w ∈ degreeTwo G (G.neighborFinset x) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw, hw⟩
  have hpos := Finset.card_pos.mpr ⟨w, hm⟩
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
