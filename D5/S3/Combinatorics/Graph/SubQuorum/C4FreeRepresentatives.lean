/- GID: D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim; result=D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result; claim=D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim
   digest: Pappus dissociation refutation of the cubic C4-free half-order bound. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4RepresentativeBounds
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.CardIntervalMod

/-! The actual Pappus certificates use Sahbi source PR #28593 at revision
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The Pappus dissociation ten-set refutes the cubic C4-free half-order claim.
Its parity coloring comes from the certified adjacency table. The side counts
used in the representative bounds are an application of the general parity count. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
open StarFormingDissociationRefutation
open StarForming
open scoped BigOperators
open DoubleStarGrafting

def pappusNeighbors (vertex : Fin 18) : List Nat :=
  match vertex.val with
  | 0 => [1, 5, 17]
  | 1 => [0, 2, 8]
  | 2 => [1, 3, 13]
  | 3 => [2, 4, 10]
  | 4 => [3, 5, 15]
  | 5 => [0, 4, 6]
  | 6 => [5, 7, 11]
  | 7 => [6, 8, 14]
  | 8 => [1, 7, 9]
  | 9 => [8, 10, 16]
  | 10 => [3, 9, 11]
  | 11 => [6, 10, 12]
  | 12 => [11, 13, 17]
  | 13 => [2, 12, 14]
  | 14 => [7, 13, 15]
  | 15 => [4, 14, 16]
  | 16 => [9, 15, 17]
  | 17 => [0, 12, 16]
  | _ => []

def pappusSelected : List Nat := [0, 1, 4, 6, 7, 9, 10, 12, 13, 15]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem pappus_regular_bipartite_certificate :
    (∀ vertex : Fin 18, (pappusNeighbors vertex).length = 3 ∧
      (pappusNeighbors vertex).Nodup ∧
      ∀ neighbor, neighbor ∈ pappusNeighbors vertex →
        neighbor < 18 ∧ neighbor % 2 ≠ vertex.val % 2) ∧
    (∀ first second : Fin 18,
      second.val ∈ pappusNeighbors first ↔ first.val ∈ pappusNeighbors second) := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem pappus_no_four_cycle_certificate :
    ∀ first second : Fin 18, first ≠ second →
      ((pappusNeighbors first).filter (fun vertex =>
        (pappusNeighbors second).contains vertex)).length ≤ 1 := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem pappus_dissociation_certificate :
    pappusSelected.length = 10 ∧ pappusSelected.Nodup ∧
    (∀ vertex, vertex ∈ pappusSelected → vertex < 18) ∧
    (∀ vertex : Fin 18, vertex.val ∈ pappusSelected →
      ((pappusNeighbors vertex).filter (fun neighbor =>
        pappusSelected.contains neighbor)).length ≤ 1) := by
  decide


def pappusGraph : SimpleGraph (Fin 18) where
  Adj v w := w.val ∈ pappusNeighbors v
  symm := ⟨fun v w h => (pappus_regular_bipartite_certificate.2 v w).mp h⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel pappusGraph.Adj := fun v w => inferInstanceAs
  (Decidable (w.val ∈ pappusNeighbors v))

def pappusSet : Finset (Fin 18) := Finset.univ.filter (fun v => v.val ∈ pappusSelected)

private theorem pappus_degree_bridge : ∀ v : Fin 18,
    DegreeCapacity.degree pappusGraph v = (pappusNeighbors v).length := by decide +kernel

private theorem pappus_common_bridge : ∀ a b : Fin 18,
    (Finset.univ.filter (fun v => pappusGraph.Adj a v ∧ pappusGraph.Adj b v)).card =
      ((pappusNeighbors a).filter (fun v => (pappusNeighbors b).contains v)).length := by
  decide +kernel

private theorem pappus_selection_bridge : ∀ v : Fin 18,
    (pappusSet.filter (pappusGraph.Adj v)).card =
      ((pappusNeighbors v).filter (fun w => pappusSelected.contains w)).length := by
  decide +kernel

def pappusColor (v : Fin 18) : Bool := decide (v.val % 2 = 1)

theorem pappusColor_valid : ∀ v w, pappusGraph.Adj v w → pappusColor v ≠ pappusColor w := by
  intro v w hadj hcolor
  have hparity := ((pappus_regular_bipartite_certificate.1 v).2.2 w.val hadj).2
  simp only [pappusColor] at hcolor
  have hv := Nat.mod_lt v.val (by decide : 0 < 2)
  have hw := Nat.mod_lt w.val (by decide : 0 < 2)
  by_cases h : v.val % 2 = 1
  · have he : w.val % 2 = 1 := by simpa [h, eq_comm] using hcolor
    exact hparity (he.trans h.symm)
  · have he : w.val % 2 ≠ 1 := by simpa [h, eq_comm] using hcolor
    omega

/-- The two parity classes on an even initial interval have equal size. -/
theorem paritySide_card (n : ℕ) (c : Bool) :
    (Finset.univ.filter (fun v : Fin (2 * n) => decide (v.val % 2 = 1) = c)).card = n := by
  let p (i : ℕ) : Prop := i ≡ c.toNat [MOD 2]
  have hp (v : Fin (2 * n)) : decide (v.val % 2 = 1) = c ↔ p v.val := by
    have hv := Nat.mod_lt v.val (by decide : 0 < 2)
    cases c <;> simp [p, Nat.ModEq] <;> omega
  simp_rw [hp]
  have hcard := Nat.count_modEq_card (b := 2 * n) (r := 2) (by decide) c.toNat
  rw [Nat.count_eq_card_filter_range] at hcard
  calc
    _ = (((Finset.univ : Finset (Fin (2 * n))).map Fin.valEmbedding).filter p).card :=
      (Finset.card_map _).symm.trans (congrArg Finset.card
        (Finset.filter_map (s := Finset.univ) (f := Fin.valEmbedding) (p := p))).symm
    _ = n := by
      rw [Fin.map_valEmbedding_univ, Nat.Iio_eq_range]
      simpa [p, Nat.mul_comm 2 n] using hcard

/-- The exact supplier table gives actual cubic bipartiteness and no four-cycle. -/
theorem pappus_class : pappusGraph.Colorable 2 ∧
    (∀ v, DegreeCapacity.degree pappusGraph v = 3) ∧ NoFourCycle pappusGraph.Adj := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨SimpleGraph.Coloring.mk
      (fun v => (⟨v.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
    intro a b hab he
    apply pappusColor_valid a b hab
    unfold pappusColor
    have hparity : a.val % 2 = b.val % 2 := congrArg Fin.val he
    rw [hparity]
  · intro v
    rw [pappus_degree_bridge]
    exact (pappus_regular_bipartite_certificate.1 v).1
  · intro a b x y hab hxy hax hay hbx hby h1 h2 h3 h4
    have hc := pappus_no_four_cycle_certificate a b hab
    rw [← pappus_common_bridge] at hc
    have hi := Finset.card_le_one.mp hc
    exact hxy (hi x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1,h3⟩)
      y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2,h4⟩))

/-- The source ten-set is transported to the actual canonical finite selection. -/
theorem pappus_selection : IsKIndependent pappusGraph 2 pappusSet ∧ pappusSet.card = 10 := by
  constructor
  · intro v hv
    have hh := pappus_dissociation_certificate.2.2.2 v (Finset.mem_filter.mp hv).2
    rw [pappus_selection_bridge]
    omega
  · decide +kernel

/-- The canonical maximum is exactly 10, without enumerating all graph subsets. -/
theorem beta_pappus : beta pappusGraph 2 = 10 := by
  have hlo : pappusSet.card ≤ beta pappusGraph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,pappus_selection.1⟩)
  rw [pappus_selection.2] at hlo
  have hm := beta_le_sf pappusGraph
  have hu := DegreeCapacity.sf_regular_bound pappusGraph 3 (by decide) pappus_class.2.1
  norm_num at hu
  omega

/-- The cubic C4-free half-order identification cannot extend to order 18. -/
def claim : Prop := ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj],
  G.Colorable 2 → (∀ v, DegreeCapacity.degree G v = 3) → NoFourCycle G.Adj →
    2 * beta G 2 ≤ 18

set_option maxRecDepth 8192 in
theorem result : ¬ claim := by
  intro h
  have hh := h pappusGraph pappus_class.1 pappus_class.2.1 pappus_class.2.2
  rw [beta_pappus] at hh
  omega

end D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
