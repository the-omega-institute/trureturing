/- GID: D5/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd digit rows force a deficit in directed slot incidence with unique target ownership. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.OddSlotTargetDeficit

open scoped BigOperators

variable {p : Nat} {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Directed incidence of used reading slots. No acyclicity or unique-parent
condition is imposed. Every nonempty successor set has one target control. -/
structure SlotGraph (p : Nat) (Q : Type) [Fintype Q] [DecidableEq Q] where
  root : Q
  used : Finset (Q × Fin p)
  next : Q × Fin p → Finset (Q × Fin p)
  target : Q × Fin p → Q
  target_eq : ∀ u v, v ∈ next u → v.1 = target u
  source_used : ∀ u, (next u).Nonempty → u ∈ used
  target_used : ∀ u v, v ∈ next u → v ∈ used
  root_used : ∀ b, (root, b) ∈ used
  root_no_incoming : ∀ u b, (root, b) ∉ next u
  nonroot_incoming : ∀ v ∈ used, v.1 ≠ root → ∃ u, v ∈ next u
  at_most_two : ∀ u, (next u).card ≤ 2

namespace SlotGraph

variable (G : SlotGraph p Q)

noncomputable def incoming (v : Q × Fin p) : Finset (Q × Fin p) :=
  Finset.univ.filter (fun u => v ∈ G.next u)

noncomputable def missing (q : Q) : Nat :=
  (Finset.univ.filter (fun b : Fin p => (q, b) ∉ G.used)).card

noncomputable def excess (q : Q) : Nat :=
  ∑ b : Fin p, (G.incoming (q, b)).card - 1

noncomputable def singles (q : Q) : Nat :=
  (Finset.univ.filter (fun u => G.target u = q ∧ (G.next u).card = 1)).card

private noncomputable def predecessors (q : Q) : Finset (Q × Fin p) :=
  Finset.univ.filter (fun u => G.target u = q ∧ (G.next u).Nonempty)

/-- A zero-deficit row is covered exactly once by two-slot successor sets.
The ownership field makes these sets lie in the same target row. -/
private theorem zero_deficit_even (q : Q) (hq : q ≠ G.root)
    (hz : G.missing q = 0) (hh : G.excess q = 0) (hn : G.singles q = 0) :
    Even p := by
  classical
  have all_used (b : Fin p) : (q, b) ∈ G.used := by
    have empty := Finset.card_eq_zero.mp hz
    by_contra hb
    have : b ∈ Finset.univ.filter (fun b : Fin p => (q, b) ∉ G.used) := by simp [hb]
    rw [empty] at this
    exact Finset.notMem_empty _ this
  have indegree (b : Fin p) : (G.incoming (q, b)).card ≤ 1 := by
    have hterm := Finset.single_le_sum (fun b _ => Nat.zero_le
      ((G.incoming (q, b)).card - 1)) (Finset.mem_univ b)
    change (G.incoming (q, b)).card - 1 ≤ G.excess q at hterm
    omega
  have no_single (u : Q × Fin p) (hu : G.target u = q) : (G.next u).card ≠ 1 := by
    intro hc
    have empty := Finset.card_eq_zero.mp hn
    have : u ∈ Finset.univ.filter
        (fun u => G.target u = q ∧ (G.next u).card = 1) := by simp [hu, hc]
    rw [empty] at this
    exact Finset.notMem_empty _ this
  have two (u : Q × Fin p) (hu : u ∈ G.predecessors q) : (G.next u).card = 2 := by
    obtain ⟨_, ht, he⟩ := Finset.mem_filter.mp hu
    have pos := Finset.card_pos.mpr he
    have bound := G.at_most_two u
    have ne := no_single u ht
    omega
  have disjoint : (↑(G.predecessors q) : Set (Q × Fin p)).PairwiseDisjoint G.next := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro z hzu hzv
    have ez : z.1 = q := (G.target_eq u z hzu).trans (Finset.mem_filter.mp hu).2.1
    have bound : (G.incoming z).card ≤ 1 := by
      obtain ⟨qz, b⟩ := z
      dsimp at ez
      subst qz
      exact indegree b
    have equal := Finset.card_le_one.mp bound
    exact huv (equal u (by simp [incoming, hzu]) v (by simp [incoming, hzv]))
  have cover : (G.predecessors q).biUnion G.next =
      Finset.univ.image (fun b : Fin p => (q, b)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, hv⟩ := Finset.mem_biUnion.mp hv
      have eq : v.1 = q := (G.target_eq u v hv).trans (Finset.mem_filter.mp hu).2.1
      exact Finset.mem_image.mpr ⟨v.2, Finset.mem_univ _, by exact Prod.ext eq.symm rfl⟩
    · intro hv
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨u, hu⟩ := G.nonroot_incoming (q, b) (all_used b) hq
      apply Finset.mem_biUnion.mpr
      refine ⟨u, ?_, hu⟩
      simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(G.target_eq u (q, b) hu).symm, ⟨_, hu⟩⟩
  have count := Finset.card_biUnion disjoint
  rw [cover, Finset.card_image_of_injective _ (fun a b h => Prod.mk.inj h |>.2)] at count
  simp only [Finset.card_univ, Fintype.card_fin] at count
  have sizes : (∑ u ∈ G.predecessors q, (G.next u).card) =
      (G.predecessors q).card * 2 := Finset.sum_const_nat two
  rw [sizes] at count
  exact ⟨(G.predecessors q).card, by omega⟩

/-- Every nonroot row over an odd alphabet has an unused slot, a repeated
incoming incidence, or a one-successor predecessor owned by that row. -/
private theorem target_deficit (hp : Odd p) (q : Q) (hq : q ≠ G.root) :
    1 ≤ G.missing q + G.excess q + G.singles q := by
  by_contra bad
  have hz : G.missing q = 0 := by omega
  have hh : G.excess q = 0 := by omega
  have hn : G.singles q = 0 := by omega
  exact hp.not_even (G.zero_deficit_even q hq hz hh hn)

/-- Local and summed target deficits use the same incidence graph. Cycles
and mergers contribute to excess and are not removed by a tree unfolding. -/
theorem result (hp : Odd p) :
    (∀ q, q ≠ G.root → 1 ≤ G.missing q + G.excess q + G.singles q) ∧
    Fintype.card Q - 1 ≤
      (∑ q, G.missing q) + (∑ q, G.excess q) + (∑ q, G.singles q) := by
  classical
  refine ⟨G.target_deficit hp, ?_⟩
  have local_bound : ∀ q ∈ Finset.univ.erase G.root,
      1 ≤ G.missing q + G.excess q + G.singles q := by
    intro q hq
    exact G.target_deficit hp q (Finset.mem_erase.mp hq).1
  have sum_bound := Finset.sum_le_sum local_bound
  have extend : (∑ q ∈ Finset.univ.erase G.root,
      (G.missing q + G.excess q + G.singles q)) ≤
      ∑ q : Q, (G.missing q + G.excess q + G.singles q) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  have card : (Finset.univ.erase G.root).card = Fintype.card Q - 1 := by simp
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at sum_bound
  rw [card] at sum_bound
  simpa only [Finset.sum_add_distrib] using sum_bound.trans extend

end SlotGraph
end D5.S3.ObserverMemory.Algorithms.OddSlotTargetDeficit
