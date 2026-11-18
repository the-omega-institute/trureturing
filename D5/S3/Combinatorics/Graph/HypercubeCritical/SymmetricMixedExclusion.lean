/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: The actual mixed high profiles force a closed Y and a disjoint high eight-cycle. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCycle
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricActualHighProfiles
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPairDeficit
import Batteries.Tactic.OpenPrivate

/-! Actual mixed profile exclusion by Y-complement low exhaustion. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedExclusion

open SimpleGraph GirthSliceCounting
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private mixed_high_cycle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCycle
open private High graph side graph_degree symmetric_high_graph actual_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private highDegree highTypeA highTypeB symmetric_high_profile_saturation from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
open private sideDegreeTuple side_degree_tuple neighbor_degree_sum actual_high_profiles from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricActualHighProfiles
open private CycleLowData CycleLowData.partner CycleLowData.low CycleLowData.low_degree
  CycleLowData.partner_adj CycleLowData.cycle_adj
  actual_high_cycle_low_saturation low_has_exact_cycle_endpoint
  cycle_parity_sides cycle_partner_sides leaf_low_neighbors_are_antipodal from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation
open private unique_low_partner from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
open private high_low_ne from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPairDeficit
open private three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem adjacent_partner_parity {c : Fin 8 → V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    (h0 : c 0 ∈ L) (d : CycleLowData G c)
    {i j : Fin 8} (hij : G.Adj ((CycleLowData.partner d) i) ((CycleLowData.partner d) j)) :
    i.val % 2 ≠ j.val % 2 := by
  obtain ⟨hcL, hcR⟩ := cycle_parity_sides hpart c hcycle h0
  obtain ⟨hiL, hiR⟩ := cycle_partner_sides hpart d i
  obtain ⟨hjL, hjR⟩ := cycle_partner_sides hpart d j
  intro he
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 = 0 := he ▸ hi
    have hpL := hjL.mpr (hcL j hj)
    have hpR := hpart.mem_of_mem_adj (hiL.mpr (hcL i hi)) hij
    exact Set.disjoint_left.mp hpart.disjoint hpL hpR
  · have hi1 : i.val % 2 = 1 := by omega
    have hj1 : j.val % 2 = 1 := he ▸ hi1
    have hpR := hjR.mpr (hcR j hj1)
    have hpL := hpart.symm.mem_of_mem_adj (hiR.mpr (hcR i hi1)) hij
    exact Set.disjoint_left.mp hpart.disjoint hpL hpR

/-- A high-graph degree-two point outside an actual C8 cannot be adjacent to
an outside high-graph leaf. The low exhaustion is global, but no high-degree-two
coverage assumption is made. -/
private theorem outside_two_leaf_impossible
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (e : cycleGraph 8 ↪g graph G) (he2 : ∀ i, (graph G).degree (e i) = 2)
    (s r : High G) (hs2 : (graph G).degree s = 2) (hr1 : (graph G).degree r = 1)
    (hsr : (graph G).Adj s r) (hsout : ∀ i, s ≠ e i) (hrout : ∀ i, r ≠ e i) :
    False := by
  let c : Fin 8 → V := fun i => (e i).val
  have hc : Function.Injective c := fun i j he => e.injective (Subtype.ext he)
  have hc3 : ∀ i, G.degree (c i) = 3 := fun i => (e i).property
  have hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j) :=
    fun _ _ h => e.map_adj_iff.mpr h
  have hsout' : ∀ i, s.val ≠ c i := fun i he => hsout i (Subtype.ext he)
  have hrout' : ∀ i, r.val ≠ c i := fun i he => hrout i (Subtype.ext he)
  obtain ⟨d⟩ := actual_high_cycle_low_saturation hpart hdeg hlow hg hL2 hR2 e he2
  obtain ⟨i, _hi, _hN, hfiber⟩ := leaf_low_neighbors_are_antipodal hpart hdeg hg
    c hc hc3 hcycle d r.property ((graph_degree G r).symm.trans hr1) hrout'
  obtain ⟨l, _p, hl2, _hp3, _hsp, hsl, _hpl, _hNl, _hu, _hwl⟩ :=
    unique_low_partner hdeg hlow s.property ((graph_degree G s).symm.trans hs2)
  obtain ⟨j, hjl, hNl, _hjuniq, _hjout⟩ := low_has_exact_cycle_endpoint d hl2
  have hps : (CycleLowData.partner d) j = s.val := by
    have hm : s.val ∈ G.neighborFinset l := (G.mem_neighborFinset _ _).mpr hsl.symm
    rw [hNl] at hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact False.elim (hsout' j he)
    · exact (Finset.mem_singleton.mp he).symm
  have hpi : (CycleLowData.partner d) i = r.val := (hfiber i).mpr (Or.inl rfl)
  have hpij : G.Adj ((CycleLowData.partner d) i) ((CycleLowData.partner d) j) := by
    rw [hpi, hps]
    exact hsr.symm
  have hparity : i.val % 2 ≠ j.val % 2 := by
    rcases actual_partition hpart hdeg (c 0) with h0 | h0
    · exact adjacent_partner_parity hpart hcycle h0 d hpij
    · exact adjacent_partner_parity hpart.symm hcycle h0 d hpij
  have hnear : ∀ i j : Fin 8, i.val % 2 ≠ j.val % 2 →
      (cycleGraph 8).Adj j i ∨ (cycleGraph 8).Adj j (i + 4) := by
    decide +kernel
  obtain ⟨k, hk, hjk⟩ : ∃ k : Fin 8, (k = i ∨ k = i + 4) ∧
      (cycleGraph 8).Adj j k := by
    rcases hnear i j hparity with h | h
    · exact ⟨i, Or.inl rfl, h⟩
    · exact ⟨i + 4, Or.inr rfl, h⟩
  have hpk : (CycleLowData.partner d) k = r.val := (hfiber k).mpr hk
  have hrlow : G.Adj r.val ((CycleLowData.low d) k) := by simpa only [hpk] using (CycleLowData.partner_adj d) k
  have hslow : G.Adj s.val ((CycleLowData.low d) j) := by simpa only [hps] using (CycleLowData.partner_adj d) j
  have hwalk : r.val = (CycleLowData.low d) j := by
    rcases actual_partition hpart hdeg s.val with hsL | hsR
    · exact (three_walk_endpoint_injective hpart hg hsL hsL
        hsr hrlow ((CycleLowData.cycle_adj d) k).symm hslow ((CycleLowData.cycle_adj d) j).symm (hcycle j k hjk)
        (high_low_ne s.property ((CycleLowData.low_degree d) k)) (hrout' k) (hsout' j)
        (high_low_ne (hc3 k) ((CycleLowData.low_degree d) j)).symm ⟨rfl, rfl⟩).2.1
    · exact (three_walk_endpoint_injective hpart.symm hg hsR hsR
        hsr hrlow ((CycleLowData.cycle_adj d) k).symm hslow ((CycleLowData.cycle_adj d) j).symm (hcycle j k hjk)
        (high_low_ne s.property ((CycleLowData.low_degree d) k)) (hrout' k) (hsout' j)
        (high_low_ne (hc3 k) ((CycleLowData.low_degree d) j)).symm ⟨rfl, rfl⟩).2.1
  exact high_low_ne r.property ((CycleLowData.low_degree d) j) hwalk

/-- The actual A/B profile is impossible under the original eleven/eleven and
four/four premises, without any cube-embedding premise. -/
private theorem actual_ab_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLA : highTypeA G (degreeThree G L))
    (hRB : highTypeB G (degreeThree G R)) : False := by
  obtain ⟨_, _, hcard, hgg, hpartH, _⟩ :=
    symmetric_high_graph hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨hhigh, _, _⟩ := actual_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  have hactualL : sideDegreeTuple G L = (1, 6, 0) := by
    rw [side_degree_tuple]
    exact hLA
  have hactualR : sideDegreeTuple G R = (2, 4, 1) := by
    rw [side_degree_tuple]
    exact hRB
  obtain ⟨hLs, _, _, _⟩ :=
    symmetric_high_profile_saturation hpart hdeg hlow hg hL hR hL2 hR2
  have hsatL : ∀ x ∈ side G L, (∑ y ∈ (graph G).neighborFinset x, (graph G).degree y) =
      (graph G).degree x + 2 := by
    intro x hx
    rw [neighbor_degree_sum, graph_degree]
    exact hLs hRB x.val
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, x.property⟩)
  obtain ⟨s, r, hs2, hr1, hsr, e, he2, hsout, hrout⟩ :=
    mixed_high_cycle (graph G) hpartH hcard hgg hhigh hactualL hactualR hsatL
  exact outside_two_leaf_impossible hpart hdeg hlow hg hL2 hR2 e he2 s r hs2 hr1 hsr hsout hrout

private theorem actual_ba_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLB : highTypeB G (degreeThree G L))
    (hRA : highTypeA G (degreeThree G R)) : False := by
  exact actual_ab_excluded hpart.symm hdeg hlow hg hR hL hR2 hL2 hRA hLB

#print axioms outside_two_leaf_impossible
#print axioms actual_ab_excluded
#print axioms actual_ba_excluded

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedExclusion
