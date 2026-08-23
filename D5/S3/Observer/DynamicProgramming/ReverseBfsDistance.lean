/- GID: D5/S3/Observer/DynamicProgramming/ReverseBfsDistance
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/ReverseBfsDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reverse breadth-first search computes every first-separation depth quadratically. -/

import D5.S3.Observer.Separation.FiniteFutureCongruence
import Mathlib.Data.Finset.Card

/- Library-search audit trail (2026-08-23):
   * Exact family hit `observedAt` supplies the canonical deterministic
     update/readout semantics and is imported rather than redeclared.
   * Pinned Mathlib exact hits `Nat.find_spec`, `Nat.find_min'`,
     `Finset.card_image_of_injective`, and `Fintype.card_prod` supply the
     least-visit and explicit-edge-table counts and are applied directly.
   * Repository and pinned-Mathlib searches for reverse breadth-first search,
     pair distance, and explicit pair-edge-table complexity found no theorem
     packaging correctness with both quadratic resource clauses. -/

noncomputable section

namespace D5.S3.Observer.DynamicProgramming.ReverseBfsDistance

open D5.S3.Observer.Separation.FiniteFutureCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The unique forward successor of a pair of deterministic states. -/
def pairSuccessor {Y : Type*} (update : Y -> Y) (pair : Y × Y) : Y × Y :=
  (update pair.1, update pair.2)

/-- The initial multi-source table of pairs whose current readouts differ. -/
def mismatchTable {Y O : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq O]
    (readout : Y -> O) : Finset (Y × Y) :=
  Finset.univ.filter fun pair => Not (readout pair.1 = readout pair.2)

/-- One cumulative reverse-search expansion through the deterministic pair edge. -/
def reverseExpand {Y : Type*} [Fintype Y] [DecidableEq Y]
    (update : Y -> Y) (visited : Finset (Y × Y)) : Finset (Y × Y) :=
  visited ∪ Finset.univ.filter fun pair => pairSuccessor update pair ∈ visited

/-- Pairs visited by the multi-source reverse search in at most `depth` edges. -/
def reverseVisited {Y O : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq O]
    (update : Y -> Y) (readout : Y -> O) : Nat -> Finset (Y × Y)
  | 0 => mismatchTable readout
  | depth + 1 => reverseExpand update (reverseVisited update readout depth)

/-- The first reverse-search visit depth, with `none` for an unvisited pair. -/
def reverseBfsDistance {Y O : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq O]
    (update : Y -> Y) (readout : Y -> O) (pair : Y × Y) : Option Nat := by
  letI : Decidable (exists depth, pair ∈ reverseVisited update readout depth) :=
    Classical.propDecidable _
  exact if visited : exists depth, pair ∈ reverseVisited update readout depth then
      some (Nat.find visited)
    else
      none

/-- The source-semantic first future readout mismatch, with `none` for infinity. -/
def exactSeparationDepth {Y O : Type*} [DecidableEq O]
    (update : Y -> Y) (readout : Y -> O) (pair : Y × Y) : Option Nat := by
  letI : Decidable (exists depth,
      Not (observedAt update readout depth pair.1 =
        observedAt update readout depth pair.2)) := Classical.propDecidable _
  exact if separates : exists depth,
        Not (observedAt update readout depth pair.1 =
          observedAt update readout depth pair.2) then
      some (Nat.find separates)
    else
      none

/-- The explicit reversed edge table stores exactly one edge for every ordered
state pair. -/
def explicitReverseEdgeTable {Y : Type*} [Fintype Y] [DecidableEq Y]
    (update : Y -> Y) : Finset ((Y × Y) × (Y × Y)) :=
  Finset.univ.image fun pair => (pairSuccessor update pair, pair)

/-- Unit-cost work for one queue visit per pair and one scan per reversed edge. -/
def reverseBfsTimeBudget {Y : Type*} [Fintype Y] [DecidableEq Y]
    (update : Y -> Y) : Nat :=
  Fintype.card (Y × Y) + (explicitReverseEdgeTable update).card

/-- Storage for the explicit reversed edges, a distance table, and a queue with
one slot per ordered pair. -/
def reverseBfsSpaceBudget {Y : Type*} [Fintype Y] [DecidableEq Y]
    (update : Y -> Y) : Nat :=
  (explicitReverseEdgeTable update).card +
    Fintype.card (Y × Y) + Fintype.card (Y × Y)

private theorem mem_reverseVisited_iff {Y O : Type*}
    [Fintype Y] [DecidableEq Y] [DecidableEq O]
    (update : Y -> Y) (readout : Y -> O) (depth : Nat) (pair : Y × Y) :
    pair ∈ reverseVisited update readout depth <->
      exists witness, witness <= depth /\
        Not (observedAt update readout witness pair.1 =
          observedAt update readout witness pair.2) := by
  induction depth generalizing pair with
  | zero =>
      simp [reverseVisited, mismatchTable, observedAt]
  | succ depth ih =>
      rw [reverseVisited]
      simp only [reverseExpand, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [ih, ih]
      constructor
      · rintro (current | next)
        · rcases current with ⟨witness, bound, mismatch⟩
          exact ⟨witness, bound.trans (Nat.le_succ depth), mismatch⟩
        · rcases next with ⟨witness, bound, mismatch⟩
          refine ⟨witness + 1, Nat.succ_le_succ bound, ?_⟩
          simpa [pairSuccessor, observedAt, Function.iterate_succ_apply] using mismatch
      · rintro ⟨witness, bound, mismatch⟩
        cases witness with
        | zero =>
            left
            exact ⟨0, Nat.zero_le depth, mismatch⟩
        | succ witness =>
            right
            have witnessBound : witness <= depth :=
              Nat.le_of_succ_le_succ bound
            refine ⟨witness, witnessBound, ?_⟩
            simpa [pairSuccessor, observedAt, Function.iterate_succ_apply] using mismatch

private theorem reverse_distance_eq_exact {Y O : Type*}
    [Fintype Y] [DecidableEq Y] [DecidableEq O]
    (update : Y -> Y) (readout : Y -> O) :
    reverseBfsDistance update readout = exactSeparationDepth update readout := by
  classical
  funext pair
  by_cases separates : exists depth,
      Not (observedAt update readout depth pair.1 =
        observedAt update readout depth pair.2)
  · have visited : exists depth, pair ∈ reverseVisited update readout depth :=
      ⟨Nat.find separates,
        (mem_reverseVisited_iff update readout (Nat.find separates) pair).2
          ⟨Nat.find separates, le_rfl, Nat.find_spec separates⟩⟩
    rw [reverseBfsDistance, dif_pos visited, exactSeparationDepth, dif_pos separates]
    congr 1
    apply Nat.le_antisymm
    · apply Nat.find_min' visited
      exact (mem_reverseVisited_iff update readout (Nat.find separates) pair).2
        ⟨Nat.find separates, le_rfl, Nat.find_spec separates⟩
    · rcases (mem_reverseVisited_iff update readout (Nat.find visited) pair).1
        (Nat.find_spec visited) with ⟨witness, bound, mismatch⟩
      exact (Nat.find_min' separates mismatch).trans bound
  · have unvisited : Not (exists depth,
        pair ∈ reverseVisited update readout depth) := by
      rintro ⟨depth, member⟩
      rcases (mem_reverseVisited_iff update readout depth pair).1 member with
        ⟨witness, _, mismatch⟩
      exact separates ⟨witness, mismatch⟩
    rw [reverseBfsDistance, dif_neg unvisited,
      exactSeparationDepth, dif_neg separates]

private theorem explicit_reverse_edge_card {Y : Type*}
    [Fintype Y] [DecidableEq Y] (update : Y -> Y) :
    (explicitReverseEdgeTable update).card = Fintype.card Y ^ 2 := by
  rw [explicitReverseEdgeTable,
    Finset.card_image_of_injective Finset.univ]
  · simp [Fintype.card_prod, pow_two]
  · intro first second equalEdges
    exact congrArg Prod.snd equalEdges

/-- Reverse breadth-first search from every current mismatch returns exactly the
first future separation depth for every pair. With the explicit reversed pair
edge table, its unit-cost time is at most twice and its storage at most three
times the square of the state count. -/
theorem reverse_bfs_correct_and_quadratic {Y O : Type*}
    [Fintype Y] [DecidableEq Y] [DecidableEq O]
    (update : Y -> Y) (readout : Y -> O) :
    reverseBfsDistance update readout = exactSeparationDepth update readout /\
      reverseBfsTimeBudget update <= 2 * Fintype.card Y ^ 2 /\
      reverseBfsSpaceBudget update <= 3 * Fintype.card Y ^ 2 := by
  refine ⟨reverse_distance_eq_exact update readout, ?_, ?_⟩
  · rw [reverseBfsTimeBudget, explicit_reverse_edge_card]
    simp only [Fintype.card_prod, pow_two]
    omega
  · rw [reverseBfsSpaceBudget, explicit_reverse_edge_card]
    simp only [Fintype.card_prod, pow_two]
    omega

#print axioms reverse_bfs_correct_and_quadratic

end D5.S3.Observer.DynamicProgramming.ReverseBfsDistance
