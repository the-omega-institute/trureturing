/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricAAExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricAAExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: The actual A/A parameters force adjacent high leaves and a closed twelve-cycle in the actual high graph. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAAdjacent
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwelveCapacity
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAExclusion

open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable

open private small_two_regular_cycle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle
open private High graph graph_degree actual_partition symmetric_high_graph from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private highDegree highTypeA highProfile symmetric_high_profiles from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
open private typeA_other_high_degree_two actual_typeA_leaves_adjacent from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAAdjacent
open private global_degree_two_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition

private theorem cycle_away_from_adjacent_leaves
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) (hcard : Fintype.card X = 14)
    (hg : (8 : ℕ∞) ≤ H.egirth)
    {a b : X} (hab : H.Adj a b)
    (ha : H.degree a = 1) (hb : H.degree b = 1)
    (hother : ∀ x, x ≠ a → x ≠ b → H.degree x = 2) :
    ∃ e : cycleGraph 12 ↪g H, ∀ i, H.degree (e i) = 2 := by
  let T : Set X := {x | x ≠ a ∧ x ≠ b}
  have hba : b ≠ a := hab.ne.symm
  have hT : Fintype.card T = 12 := by
    rw [← Set.toFinset_card]
    have he : T.toFinset = (Finset.univ.erase a).erase b := by
      ext x
      simp [T, and_comm]
    rw [he]
    simp [Finset.card_erase_of_mem, hba, hcard]
  let K : SimpleGraph T := H.induce T
  have hne : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty T := hne
  have hmem (x : X) : x ∈ T ↔ x ≠ a ∧ x ≠ b := Iff.rfl
  have hNb : H.neighborFinset b = {a} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(H.mem_neighborFinset _ _).mpr hab.symm, ?_⟩
    intro x hx
    exact Finset.card_le_one.mp (by simpa using hb.le) x hx a
      ((H.mem_neighborFinset _ _).mpr hab.symm)
  have hNa' : H.neighborFinset a = {b} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(H.mem_neighborFinset _ _).mpr hab, ?_⟩
    intro x hx
    exact Finset.card_le_one.mp (by simpa using ha.le) x hx b
      ((H.mem_neighborFinset _ _).mpr hab)
  have hdegree (x : T) : K.degree x = 2 := by
    have hx := (hmem x.val).mp x.property
    have hsub : H.neighborSet x.val ⊆ T := by
      intro y hxy
      apply (hmem y).mpr
      constructor
      · intro hy
        have hm : x.val ∈ H.neighborFinset a :=
          (H.mem_neighborFinset _ _).mpr (hy ▸ hxy.symm)
        rw [hNa'] at hm
        exact hx.2 (Finset.mem_singleton.mp hm)
      · intro hy
        have hm : x.val ∈ H.neighborFinset b :=
          (H.mem_neighborFinset _ _).mpr (hy ▸ hxy.symm)
        rw [hNb] at hm
        exact hx.1 (Finset.mem_singleton.mp hm)
    exact (H.degree_induce_of_neighborSet_subset hsub).trans (hother x.val hx.1 hx.2)
  have hKg : (8 : ℕ∞) ≤ K.egirth :=
    hg.trans (SimpleGraph.Embedding.induce T).isContained.egirth_le
  obtain ⟨_, p, _, hlen, _, hiso⟩ := small_two_regular_cycle K hdegree hKg (by omega)
  have hl : p.length = 12 := hlen.trans hT
  obtain ⟨e⟩ : Nonempty (cycleGraph 12 ≃g K) := hl ▸ hiso
  refine ⟨{ toFun := fun i => (e i).val
            inj' := fun i j he => e.injective (Subtype.ext he)
            map_rel_iff' := by intro i j; exact e.map_rel_iff }, ?_⟩
  intro i
  exact hother (e i).val ((hmem _).mp (e i).property).1
    ((hmem _).mp (e i).property).2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem twelve_cycle_parity_sides
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (c : Fin 12 → V)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
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
  have h8 := hpart.symm.mem_of_mem_adj h7 (hcycle 7 8 (by decide +kernel))
  have h9 := hpart.mem_of_mem_adj h8 (hcycle 8 9 (by decide +kernel))
  have h10 := hpart.symm.mem_of_mem_adj h9 (hcycle 9 10 (by decide +kernel))
  have h11 := hpart.mem_of_mem_adj h10 (hcycle 10 11 (by decide +kernel))
  constructor <;> intro i hi <;> fin_cases i <;> simp_all

private theorem actual_twelve_high_cycle_impossible
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (e : cycleGraph 12 ↪g graph G)
    (he2 : ∀ i, (graph G).degree (e i) = 2) : False := by
  let c : Fin 12 → V := fun i => (e i).val
  have hc : Function.Injective c := fun i j hij => e.injective (Subtype.ext hij)
  have hc3 : ∀ i, G.degree (c i) = 3 := fun i => (e i).property
  have hchigh : ∀ i, (degreeThree G (G.neighborFinset (c i))).card = 2 :=
    fun i => (graph_degree G (e i)).symm.trans (he2 i)
  have hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j) :=
    fun _ _ h => e.map_adj_iff.mpr h
  have hcount : (degreeTwo G Finset.univ).card = 8 :=
    global_degree_two_count hpart (fun v => by rcases hdeg v with h | h <;> omega) hL2 hR2
  rcases actual_partition hpart hdeg (c 0) with h0 | h0
  · obtain ⟨hcL, hcR⟩ := twelve_cycle_parity_sides hpart c hcycle h0
    exact SymmetricTwelveCapacity.twelve_cycle_impossible
      hpart hdeg hlow hg hcount c hc hc3 hchigh hcycle hcL hcR
  · obtain ⟨hcR, hcL⟩ := twelve_cycle_parity_sides hpart.symm c hcycle h0
    exact SymmetricTwelveCapacity.twelve_cycle_impossible
      hpart.symm hdeg hlow hg hcount c hc hc3 hchigh hcycle hcR hcL

private theorem actual_aa_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLA : highTypeA G (degreeThree G L))
    (hRA : highTypeA G (degreeThree G R)) : False := by
  obtain ⟨_, _, hLp, hRp, _⟩ :=
    symmetric_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  have hleft := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hLA
  have hright := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hRA
  change ((degreeThree G L).filter fun x => highDegree G x = 1).card = 1 at hleft
  change ((degreeThree G R).filter fun x => highDegree G x = 1).card = 1 at hright
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 <
    ((degreeThree G L).filter fun x => highDegree G x = 1).card)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 <
    ((degreeThree G R).filter fun x => highDegree G x = 1).card)
  obtain ⟨ha, ha1⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hb1⟩ := Finset.mem_filter.mp hb
  have hab := actual_typeA_leaves_adjacent hpart hdeg hlow hg hL hR hL2 hR2
    hLA hRA ha hb ha1 hb1
  let A : High G := ⟨a, (Finset.mem_filter.mp ha).2⟩
  let B : High G := ⟨b, (Finset.mem_filter.mp hb).2⟩
  obtain ⟨_, _, hcard, hgg, _⟩ := symmetric_high_graph hpart hdeg hlow hg hL hR hL2 hR2
  have hA : (graph G).degree A = 1 := (graph_degree G A).trans ha1
  have hB : (graph G).degree B = 1 := (graph_degree G B).trans hb1
  have hother : ∀ x : High G, x ≠ A → x ≠ B → (graph G).degree x = 2 := by
    intro x hxa hxb
    rw [graph_degree]
    rcases actual_partition hpart hdeg x.val with hx | hx
    · exact typeA_other_high_degree_two _ hLp hLA ha ha1 x.val
        (Finset.mem_filter.mpr ⟨hx, x.property⟩) (fun he => hxa (Subtype.ext he))
    · exact typeA_other_high_degree_two _ hRp hRA hb hb1 x.val
        (Finset.mem_filter.mpr ⟨hx, x.property⟩) (fun he => hxb (Subtype.ext he))
  have hab' : (graph G).Adj A B := hab
  obtain ⟨e, he2⟩ := cycle_away_from_adjacent_leaves (graph G) hcard hgg hab' hA hB hother
  exact actual_twelve_high_cycle_impossible hpart hdeg hlow hg hL2 hR2 e he2

#check actual_aa_excluded
#print axioms actual_aa_excluded

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAExclusion
