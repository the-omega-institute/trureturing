/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: Choose the actual unique low neighbors of eight cycle points with full graph degree three and high-graph degree two. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowPairs
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition
import Batteries.Tactic.OpenPrivate

/-! Actual C8 low exhaustion and antipodal high-leaf fibers. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation

open SimpleGraph GirthSliceCounting

attribute [local instance] Classical.propDecidable

open private lowPair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private neighbor_parts_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private unique_low_partner low_pair_excludes_high_neighbor_degree_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
open private cycle_low_pairs_excluded outside_cycle_low_pair_partners_opposite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowPairs
open private High graph graph_degree actual_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private global_degree_two_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

/-- Actual vertices and incidences, including the exhaustion of all actual lows. -/
private structure CycleLowData (G : SimpleGraph V) (c : Fin 8 → V) where
  low : Fin 8 → V
  partner : Fin 8 → V
  low_injective : Function.Injective low
  low_degree : ∀ i, G.degree (low i) = 2
  partner_degree : ∀ i, G.degree (partner i) = 3
  endpoints_ne : ∀ i, c i ≠ partner i
  cycle_adj : ∀ i, G.Adj (c i) (low i)
  partner_adj : ∀ i, G.Adj (partner i) (low i)
  low_neighbors : ∀ i, G.neighborFinset (low i) = {c i, partner i}
  unique_low : ∀ i l, G.degree l = 2 → G.Adj (c i) l → l = low i
  partner_outside : ∀ i j, partner i ≠ c j
  low_exhausts : (Finset.univ : Finset (Fin 8)).image low = degreeTwo G Finset.univ

/-- Eight actual low witnesses are distinct by the no-shared-low premise.
The cardinality argument then exhausts the actual degree-two vertices. -/
private theorem cycle_low_saturation
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hcount : (degreeTwo G Finset.univ).card = 8)
    (c : Fin 8 → V)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hchigh : ∀ i, (degreeThree G (G.neighborFinset (c i))).card = 2)
    (hno : ∀ i j, i ≠ j → ¬ lowPair G (c i) (c j)) :
    Nonempty (CycleLowData G c) := by
  classical
  have hex := fun i => unique_low_partner hdeg hlow (hc3 i) (hchigh i)
  choose w p hw hp hcp hcw hpw hN _huniqP huniqW using hex
  have hwi : Function.Injective w := by
    intro i j he
    by_contra hij
    exact hno i j hij ⟨w i, hw i, hcw i, by simpa only [he] using hcw j⟩
  have hpout : ∀ i j, p i ≠ c j := by
    intro i j he
    by_cases hij : i = j
    · subst j
      exact hcp i he.symm
    · exact hno i j hij ⟨w i, hw i, hcw i, by simpa only [he] using hpw i⟩
  have hsub : (Finset.univ : Finset (Fin 8)).image w ⊆ degreeTwo G Finset.univ := by
    intro l hl
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw i⟩
  have hcard : ((Finset.univ : Finset (Fin 8)).image w).card = 8 := by
    rw [Finset.card_image_of_injOn (fun i _ j _ he => hwi he)]
    simp
  have hexhaust : (Finset.univ : Finset (Fin 8)).image w = degreeTwo G Finset.univ :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact ⟨{
    low := w
    partner := p
    low_injective := hwi
    low_degree := hw
    partner_degree := hp
    endpoints_ne := hcp
    cycle_adj := hcw
    partner_adj := hpw
    low_neighbors := hN
    unique_low := huniqW
    partner_outside := hpout
    low_exhausts := hexhaust }⟩

private theorem low_has_unique_cycle_index {c : Fin 8 → V}
    (d : CycleLowData G c) {l : V} (hl : G.degree l = 2) :
    ∃! i, d.low i = l := by
  have hm : l ∈ degreeTwo G Finset.univ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  rw [← d.low_exhausts] at hm
  obtain ⟨i, _hi, hil⟩ := Finset.mem_image.mp hm
  exact ⟨i, hil, fun j hj => d.low_injective (hj.trans hil.symm)⟩

/-- Every actual low has exactly one cycle neighbor, with its actual other
neighbor explicitly given by the partner map. -/
private theorem low_has_exact_cycle_endpoint {c : Fin 8 → V}
    (d : CycleLowData G c) {l : V} (hl : G.degree l = 2) :
    ∃ i, d.low i = l ∧ G.neighborFinset l = {c i, d.partner i} ∧
      (∀ j, G.Adj (c j) l ↔ j = i) ∧ (∀ j, d.partner i ≠ c j) := by
  obtain ⟨i, hil, _hi⟩ := low_has_unique_cycle_index d hl
  refine ⟨i, hil, ?_, ?_, d.partner_outside i⟩
  · rw [← hil]
    exact d.low_neighbors i
  · intro j
    constructor
    · intro hj
      exact d.low_injective ((d.unique_low j l hl hj).symm.trans hil.symm)
    · intro hji
      subst j
      rw [← hil]
      exact d.cycle_adj i

private theorem cycle_parity_sides
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (c : Fin 8 → V)
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    (h0 : c 0 ∈ L) :
    (∀ i, i.val % 2 = 0 → c i ∈ L) ∧
      (∀ i, i.val % 2 = 1 → c i ∈ R) := by
  have h1 := hpart.mem_of_mem_adj h0 (hcycle 0 1 (by decide +kernel))
  have h2 := hpart.symm.mem_of_mem_adj h1 (hcycle 1 2 (by decide +kernel))
  have h3 := hpart.mem_of_mem_adj h2 (hcycle 2 3 (by decide +kernel))
  have h4 := hpart.symm.mem_of_mem_adj h3 (hcycle 3 4 (by decide +kernel))
  have h5 := hpart.mem_of_mem_adj h4 (hcycle 4 5 (by decide +kernel))
  have h6 := hpart.symm.mem_of_mem_adj h5 (hcycle 5 6 (by decide +kernel))
  have h7 := hpart.mem_of_mem_adj h6 (hcycle 6 7 (by decide +kernel))
  constructor <;> intro i hi <;> fin_cases i <;> simp_all

/-- Adapter from a real induced high-graph cycle. No labeling or low-neighbor
injection is assumed; both actual bipartition orientations are handled. -/
private theorem actual_high_cycle_low_saturation
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (e : cycleGraph 8 ↪g graph G)
    (he2 : ∀ i, (graph G).degree (e i) = 2) :
    Nonempty (CycleLowData G (fun i => (e i).val)) := by
  let c : Fin 8 → V := fun i => (e i).val
  have hc : Function.Injective c := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hc3 : ∀ i, G.degree (c i) = 3 := fun i => (e i).property
  have hchigh : ∀ i, (degreeThree G (G.neighborFinset (c i))).card = 2 := by
    intro i
    exact (graph_degree G (e i)).symm.trans (he2 i)
  have hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j) := by
    intro i j hij
    exact (e.map_adj_iff).mpr hij
  have hpositive (v : V) : 0 < G.degree v := by
    rcases hdeg v with hv | hv <;> omega
  have hcount : (degreeTwo G Finset.univ).card = 8 :=
    global_degree_two_count hpart hpositive hL2 hR2
  apply cycle_low_saturation hdeg hlow hcount c hc3 hchigh
  rcases actual_partition hpart hdeg (c 0) with h0 | h0
  · obtain ⟨hcL, hcR⟩ := cycle_parity_sides hpart c hcycle h0
    exact fun i j hij => cycle_low_pairs_excluded hpart hg c hc hc3 hcycle hcL hcR hij
  · obtain ⟨hcR, hcL⟩ := cycle_parity_sides hpart.symm c hcycle h0
    exact fun i j hij =>
      cycle_low_pairs_excluded hpart.symm hg c hc hc3 hcycle hcR hcL hij

/-- In the B/B decomposition every chosen partner is an actual high-graph
leaf: degree two would put it on the cycle, and degree three has no low edge. -/
private theorem cycle_partners_are_leaves {c : Fin 8 → V}
    (d : CycleLowData G c)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hhigh : ∀ x : High G,
      (graph G).degree x = 1 ∨ (graph G).degree x = 2 ∨ (graph G).degree x = 3)
    (hcover : ∀ x : High G, (graph G).degree x = 2 ↔ ∃ i, c i = x.val) :
    ∀ i, (graph G).degree (⟨d.partner i, d.partner_degree i⟩ : High G) = 1 := by
  intro i
  let x : High G := ⟨d.partner i, d.partner_degree i⟩
  rcases hhigh x with hx1 | hx2 | hx3
  · exact hx1
  · obtain ⟨j, hj⟩ := (hcover x).mp hx2
    exact False.elim (d.partner_outside i j hj.symm)
  · have hp : lowPair G (d.partner i) (c i) :=
      ⟨d.low i, d.low_degree i, d.partner_adj i, d.cycle_adj i⟩
    have hn := low_pair_excludes_high_neighbor_degree_three hdeg (d.partner_degree i) hp
    exact False.elim (hn ((graph_degree G x).symm.trans hx3))

/-- The two actual lows of an outside high-graph leaf give precisely an
antipodal fiber of the cycle-partner map. -/
private theorem leaf_low_neighbors_are_antipodal
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 8 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    (d : CycleLowData G c)
    {t : V} (ht3 : G.degree t = 3)
    (hthigh : (degreeThree G (G.neighborFinset t)).card = 1)
    (htout : ∀ i, t ≠ c i) :
    ∃ i : Fin 8, i ≠ i + 4 ∧
      degreeTwo G (G.neighborFinset t) = {d.low i, d.low (i + 4)} ∧
      (∀ k, d.partner k = t ↔ k = i ∨ k = i + 4) := by
  have hp := neighbor_parts_card hdeg t
  have hcard : (degreeTwo G (G.neighborFinset t)).card = 2 := by omega
  obtain ⟨u, v, huv, hN⟩ := Finset.card_eq_two.mp hcard
  have hu : G.Adj t u ∧ G.degree u = 2 := by
    have hm : u ∈ degreeTwo G (G.neighborFinset t) := by rw [hN]; simp
    exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hm).1,
      (Finset.mem_filter.mp hm).2⟩
  have hv : G.Adj t v ∧ G.degree v = 2 := by
    have hm : v ∈ degreeTwo G (G.neighborFinset t) := by rw [hN]; simp
    exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hm).1,
      (Finset.mem_filter.mp hm).2⟩
  obtain ⟨i, hi, _⟩ := low_has_unique_cycle_index d hu.2
  obtain ⟨j, hj, _⟩ := low_has_unique_cycle_index d hv.2
  have hij : i ≠ j := by intro he; exact huv (hi.symm.trans ((congrArg d.low he).trans hj))
  have hpi : d.partner i = t := by
    have hm : t ∈ G.neighborFinset (d.low i) :=
      (G.mem_neighborFinset _ _).mpr (by simpa only [hi] using hu.1.symm)
    rw [d.low_neighbors i] at hm
    rcases Finset.mem_insert.mp hm with ht | ht
    · exact False.elim (htout i ht)
    · exact (Finset.mem_singleton.mp ht).symm
  have hpj : d.partner j = t := by
    have hm : t ∈ G.neighborFinset (d.low j) :=
      (G.mem_neighborFinset _ _).mpr (by simpa only [hj] using hv.1.symm)
    rw [d.low_neighbors j] at hm
    rcases Finset.mem_insert.mp hm with ht | ht
    · exact False.elim (htout j ht)
    · exact (Finset.mem_singleton.mp ht).symm
  have hti : lowPair G t (c i) := ⟨u, hu.2, hu.1, by simpa only [hi] using d.cycle_adj i⟩
  have htj : lowPair G t (c j) := ⟨v, hv.2, hv.1, by simpa only [hj] using d.cycle_adj j⟩
  have hji : j = i + 4 := by
    rcases actual_partition hpart hdeg (c 0) with h0 | h0
    · obtain ⟨hcL, hcR⟩ := cycle_parity_sides hpart c hcycle h0
      exact outside_cycle_low_pair_partners_opposite
        hpart hg c hc hc3 hcycle hcL hcR htout hij hti htj
    · obtain ⟨hcR, hcL⟩ := cycle_parity_sides hpart.symm c hcycle h0
      exact outside_cycle_low_pair_partners_opposite
        hpart.symm hg c hc hc3 hcycle hcR hcL htout hij hti htj
  have hN' : degreeTwo G (G.neighborFinset t) = {d.low i, d.low j} := by
    simpa only [hi, hj] using hN
  have hfiber : ∀ k, d.partner k = t ↔ k = i ∨ k = j := by
    intro k
    constructor
    · intro hk
      have hm : d.low k ∈ degreeTwo G (G.neighborFinset t) :=
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (by simpa only [hk] using d.partner_adj k), d.low_degree k⟩
      rw [hN'] at hm
      rcases Finset.mem_insert.mp hm with he | he
      · exact Or.inl (d.low_injective he)
      · exact Or.inr (d.low_injective (Finset.mem_singleton.mp he))
    · rintro (rfl | rfl)
      · exact hpi
      · exact hpj
  exact ⟨i, by simpa only [hji] using hij, by simpa only [hji] using hN',
    by simpa only [hji] using hfiber⟩

/-- The four actual leaf fibers are exactly the antipodal index classes.
This determines all eight low-edge endpoint pairs without enumerating graphs. -/
private theorem actual_cycle_partner_fibers
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 8 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    (d : CycleLowData G c)
    (hhigh : ∀ x : High G,
      (graph G).degree x = 1 ∨ (graph G).degree x = 2 ∨ (graph G).degree x = 3)
    (hcover : ∀ x : High G, (graph G).degree x = 2 ↔ ∃ i, c i = x.val) :
    ∀ i j, d.partner j = d.partner i ↔ j = i ∨ j = i + 4 := by
  have hrotate : ∀ a i j : Fin 8, (i = a ∨ i = a + 4) →
      ((j = a ∨ j = a + 4) ↔ (j = i ∨ j = i + 4)) := by
    decide +kernel
  have hleaf := cycle_partners_are_leaves d hdeg hhigh hcover
  intro i j
  have hpi : (degreeThree G (G.neighborFinset (d.partner i))).card = 1 :=
    (graph_degree G (⟨d.partner i, d.partner_degree i⟩ : High G)).symm.trans (hleaf i)
  obtain ⟨a, _ha, _hN, hfiber⟩ := leaf_low_neighbors_are_antipodal
    hpart hdeg hg c hc hc3 hcycle d (d.partner_degree i) hpi (d.partner_outside i)
  exact (hfiber j).trans (hrotate a i j ((hfiber i).mp rfl))

/-- All actual high-graph leaves occur as partners; there is no unaccounted
leaf outside the four antipodal fibers. -/
private theorem cycle_partners_exhaust_leaves {c : Fin 8 → V}
    (d : CycleLowData G c)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hhigh : ∀ x : High G,
      (graph G).degree x = 1 ∨ (graph G).degree x = 2 ∨ (graph G).degree x = 3)
    (hcover : ∀ x : High G, (graph G).degree x = 2 ↔ ∃ i, c i = x.val) :
    ∀ x : High G, (graph G).degree x = 1 ↔ ∃ i, d.partner i = x.val := by
  have hleaf := cycle_partners_are_leaves d hdeg hhigh hcover
  intro x
  constructor
  · intro hx1
    have hxh : (degreeThree G (G.neighborFinset x.val)).card = 1 :=
      (graph_degree G x).symm.trans hx1
    have hp := neighbor_parts_card hdeg x.val
    have hx3 := x.property
    have hc : 0 < (degreeTwo G (G.neighborFinset x.val)).card := by omega
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hc
    have hl2 := (Finset.mem_filter.mp hl).2
    have hxl := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hl).1
    obtain ⟨i, hi, _⟩ := low_has_unique_cycle_index d hl2
    have hm : x.val ∈ G.neighborFinset (d.low i) :=
      (G.mem_neighborFinset _ _).mpr (by simpa only [hi] using hxl.symm)
    rw [d.low_neighbors i] at hm
    rcases Finset.mem_insert.mp hm with he | he
    · have hx2 := (hcover x).mpr ⟨i, he.symm⟩
      omega
    · exact ⟨i, (Finset.mem_singleton.mp he).symm⟩
  · rintro ⟨i, hi⟩
    have he : (⟨d.partner i, d.partner_degree i⟩ : High G) = x := Subtype.ext hi
    exact he ▸ hleaf i

/-- Actual leaf-label injection: the first four cycle partners are distinct,
and the opposite half uses precisely those same four actual vertices. -/
private theorem four_leaf_representatives {c : Fin 8 → V}
    (d : CycleLowData G c)
    (hfiber : ∀ i j, d.partner j = d.partner i ↔ j = i ∨ j = i + 4) :
    Function.Injective (fun i : Fin 4 => d.partner (i.castLE (by decide : 4 ≤ 8))) ∧
      (∀ i : Fin 8, ∃ j : Fin 4, d.partner i = d.partner (j.castLE (by decide : 4 ≤ 8))) := by
  have hsep : ∀ i j : Fin 4,
      i.castLE (by decide : 4 ≤ 8) ≠ j.castLE (by decide : 4 ≤ 8) + 4 := by
    decide +kernel
  have hrep : ∀ i : Fin 8, ∃ j : Fin 4,
      i = j.castLE (by decide : 4 ≤ 8) ∨ i = j.castLE (by decide : 4 ≤ 8) + 4 := by
    decide +kernel
  constructor
  · intro i j hij
    rcases (hfiber (j.castLE (by decide)) (i.castLE (by decide))).mp hij with he | he
    · exact Fin.ext (congrArg (fun k : Fin 8 => k.val) he)
    · exact False.elim (hsep i j he)
  · intro i
    obtain ⟨j, hj⟩ := hrep i
    exact ⟨j, (hfiber (j.castLE (by decide)) i).mpr hj⟩

/-- Each actual leaf partner lies on the same actual bipartition side as
its cycle point. Thus the two even and two odd leaf labels have fixed sides. -/
private theorem cycle_partner_sides {c : Fin 8 → V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (d : CycleLowData G c) (i : Fin 8) :
    (d.partner i ∈ L ↔ c i ∈ L) ∧ (d.partner i ∈ R ↔ c i ∈ R) := by
  constructor
  · constructor
    · intro hp
      have hw := hpart.mem_of_mem_adj hp (d.partner_adj i)
      exact hpart.symm.mem_of_mem_adj hw (d.cycle_adj i).symm
    · intro hc
      have hw := hpart.mem_of_mem_adj hc (d.cycle_adj i)
      exact hpart.symm.mem_of_mem_adj hw (d.partner_adj i).symm
  · constructor
    · intro hp
      have hw := hpart.symm.mem_of_mem_adj hp (d.partner_adj i)
      exact hpart.mem_of_mem_adj hw (d.cycle_adj i).symm
    · intro hc
      have hw := hpart.symm.mem_of_mem_adj hc (d.cycle_adj i)
      exact hpart.mem_of_mem_adj hw (d.partner_adj i).symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowSaturation
