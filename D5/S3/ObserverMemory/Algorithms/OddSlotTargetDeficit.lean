/- GID: D5/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd digit rows force a deficit in uniquely owned directed slot incidence. -/

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
  ∑ b : Fin p, ((G.incoming (q, b)).card - 1)

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
  exact (Nat.not_even_iff_odd.mpr hp) (G.zero_deficit_even q hq hz hh hn)

/-- Local and summed target deficits use the same incidence graph. Cycles
and mergers contribute to excess and are not removed by a tree unfolding. -/
private theorem summed_deficit (hp : Odd p) :
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

noncomputable def terminalCount : Nat :=
  (G.used.filter (fun u => (G.next u).card = 0)).card

private theorem edge_balance :
    (∑ u, (G.next u).card) = ∑ v, (G.incoming v).card := by
  classical
  simp only [incoming, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

private theorem incoming_balance :
    (∑ v, (G.incoming v).card) + p = G.used.card + ∑ q, G.excess q := by
  classical
  have point (v : Q × Fin p) :
      (G.incoming v).card + (if v.1 = G.root then 1 else 0) =
        (if v ∈ G.used then 1 else 0) + ((G.incoming v).card - 1) := by
    by_cases root : v.1 = G.root
    · have empty : G.incoming v = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        have hv := (Finset.mem_filter.mp hu).2
        have eq : v = (G.root, v.2) := Prod.ext root rfl
        rw [eq] at hv
        exact G.root_no_incoming u v.2 hv
      have used : v ∈ G.used := by
        have eq : v = (G.root, v.2) := Prod.ext root rfl
        rw [eq]
        exact G.root_used _
      simp [empty, root, used]
    · by_cases used : v ∈ G.used
      · obtain ⟨u, hu⟩ := G.nonroot_incoming v used root
        have pos : 0 < (G.incoming v).card :=
          Finset.card_pos.mpr ⟨u, by simp [incoming, hu]⟩
        simp only [root, used, if_false, if_true]
        omega
      · have empty : G.incoming v = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          exact used (G.target_used u v (Finset.mem_filter.mp hu).2)
        simp [empty, root, used]
  have total := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun v _ => point v)
  simp only [Finset.sum_add_distrib] at total
  have root_sum : (∑ v : Q × Fin p, if v.1 = G.root then 1 else 0) = p := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single G.root]
    · simp
    · intro q _ hq
      simp [hq]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have used_sum : (∑ v : Q × Fin p, if v ∈ G.used then 1 else 0) = G.used.card := by
    simp
  have excess_sum : (∑ v : Q × Fin p, ((G.incoming v).card - 1)) =
      ∑ q, G.excess q := by
    rw [Fintype.sum_prod_type]
    rfl
  rwa [root_sum, used_sum, excess_sum] at total

private theorem outgoing_balance :
    (∑ u, (G.next u).card) + (∑ q, G.singles q) + 2 * G.terminalCount =
      2 * G.used.card := by
  classical
  have point (u : Q × Fin p) :
      (G.next u).card + (if (G.next u).card = 1 then 1 else 0) +
        2 * (if u ∈ G.used ∧ (G.next u).card = 0 then 1 else 0) =
      2 * (if u ∈ G.used then 1 else 0) := by
    have bound := G.at_most_two u
    by_cases zero : (G.next u).card = 0
    · by_cases used : u ∈ G.used <;> simp [zero, used]
    · have used := G.source_used u (Finset.card_pos.mp (Nat.pos_of_ne_zero zero))
      by_cases one : (G.next u).card = 1
      · simp [one, used]
      · have two : (G.next u).card = 2 := by omega
        simp [two, used]
  have total := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun u _ => point u)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  have singles_sum : (∑ q, G.singles q) =
      ∑ u : Q × Fin p, if (G.next u).card = 1 then 1 else 0 := by
    simp only [singles, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases one : (G.next u).card = 1 <;> simp [one]
  have terminal_sum : (∑ u : Q × Fin p,
      if u ∈ G.used ∧ (G.next u).card = 0 then 1 else 0) = G.terminalCount := by
    unfold terminalCount
    rw [Finset.card_filter]
    have filter : (Finset.univ.filter (fun u => u ∈ G.used)) = G.used := by simp
    rw [← filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u ∈ G.used <;> by_cases hz : (G.next u).card = 0 <;> simp [hu, hz]
  have used_sum : (∑ u : Q × Fin p, if u ∈ G.used then 1 else 0) = G.used.card := by
    simp
  rwa [← singles_sum, terminal_sum, used_sum] at total

private theorem nominal_balance :
    p * Fintype.card Q = G.used.card + ∑ q, G.missing q := by
  classical
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Q × Fin p))) (p := fun v => v ∈ G.used)
  have first : (Finset.univ.filter (fun v => v ∈ G.used)).card = G.used.card := by simp
  have second : (Finset.univ.filter (fun v => v ∉ G.used)).card = ∑ q, G.missing q := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, missing, Fintype.sum_prod_type]
  rw [first, second] at split
  simpa [Fintype.card_prod, Nat.mul_comm] using split.symm

/-- Exact incidence accounting and the odd-alphabet improvement. The terminal
count is the actual number of used slots with empty successor set. -/
theorem result (hp : 2 ≤ p) (P : Nat) (hP : 1 ≤ P)
    (hterminal : G.terminalCount = p * P) :
    p * Fintype.card Q = 2 * (p * P) - p +
      (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) ∧
    2 * P - 1 ≤ Fintype.card Q ∧
    (Odd p →
      (∀ q, q ≠ G.root → 1 ≤ G.missing q + G.excess q + G.singles q) ∧
      Fintype.card Q - 1 ≤
        (∑ q, G.missing q) + (∑ q, G.excess q) + (∑ q, G.singles q) ∧
      2 * p * (P - 1) ≤ (p - 1) * (Fintype.card Q - 1)) := by
  classical
  have inc := G.incoming_balance
  have out := G.outgoing_balance
  have edges := G.edge_balance
  have nominal := G.nominal_balance
  rw [hterminal] at out
  have identity : p * Fintype.card Q + p = 2 * (p * P) +
      (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) := by omega
  have lower : 2 * P - 1 ≤ Fintype.card Q := by
    have sub : 2 * P - 1 + 1 = 2 * P := by omega
    have scaled : p * (2 * P - 1) + p = 2 * (p * P) := by
      calc
        p * (2 * P - 1) + p = p * (2 * P - 1 + 1) := by ring
        _ = p * (2 * P) := congrArg (fun n => p * n) sub
        _ = 2 * (p * P) := by ring
    have product : p * (2 * P - 1) ≤ p * Fintype.card Q := by omega
    exact Nat.le_of_mul_le_mul_left product (by omega)
  have source_identity : p * Fintype.card Q = 2 * (p * P) - p +
      (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) := by
    have scale : p ≤ 2 * (p * P) := by nlinarith
    omega
  refine ⟨source_identity, lower, ?_⟩
  intro odd
  obtain ⟨local_bound, global_bound⟩ := G.summed_deficit odd
  refine ⟨local_bound, global_bound, ?_⟩
  have qr : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨G.root⟩
  have subp : p - 1 + 1 = p := by omega
  have subP : P - 1 + 1 = P := by omega
  have subq : Fintype.card Q - 1 + 1 = Fintype.card Q := by omega
  nlinarith

end SlotGraph
end D5.S3.ObserverMemory.Algorithms.OddSlotTargetDeficit
