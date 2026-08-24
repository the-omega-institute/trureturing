/- GID: D5/S3/ObserverMemory/Algorithms/ControlledPairEdgeComplexity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ControlledPairEdgeComplexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Explicit controlled pair-edge construction has input-linear quadratic resource bounds. -/

import D5.S3.Observer.DynamicProgramming.ReverseBfsDistance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- Library-search audit trail (2026-08-25):
   * Exact repository hits `explicitReverseEdgeTable`, `reverseBfsTimeBudget`,
     `reverseBfsSpaceBudget`, and `reverse_bfs_correct_and_quadratic` supply the
     canonical per-channel reversed pair-edge table and its resource bounds.
   * Exact pinned-Mathlib hits `Finset.sum_le_sum` and `Finset.sum_const` supply
     the finite summation of those bounds over the input carrier.
   * Repository and pinned-Mathlib searches found no existing theorem packaging
     both controlled full-table resource clauses. -/

namespace D5.S3.ObserverMemory.Algorithms.ControlledPairEdgeComplexity

open D5.S3.Observer.DynamicProgramming.ReverseBfsDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Work for explicitly constructing and scanning the reversed pair-edge table
for every controlled update channel. -/
def controlledTimeBudget {U Y : Type*} [Fintype U] [Fintype Y] [DecidableEq Y]
    (update : U -> Y -> Y) : Nat :=
  Finset.univ.sum fun u => reverseBfsTimeBudget (update u)

/-- Storage for all input-labelled reversed pair edges and their per-channel
queue and distance-table accounting. -/
def controlledSpaceBudget {U Y : Type*} [Fintype U] [Fintype Y] [DecidableEq Y]
    (update : U -> Y -> Y) : Nat :=
  Finset.univ.sum fun u => reverseBfsSpaceBudget (update u)

/-- Explicitly enumerating every input channel's reversed state-pair edges has
time and storage bounded by the input count times the square of the state
count. The budgets are constructed from the canonical explicit reversed-edge
table rather than from the concluded polynomials. -/
theorem controlled_pair_edge_complexity {U Y : Type*}
    [Fintype U] [Fintype Y] [DecidableEq Y]
    (update : U -> Y -> Y) :
    controlledTimeBudget update <=
        2 * Fintype.card U * Fintype.card Y ^ 2 /\
      controlledSpaceBudget update <=
        3 * Fintype.card U * Fintype.card Y ^ 2 := by
  classical
  constructor
  · unfold controlledTimeBudget
    calc
      Finset.univ.sum (fun u => reverseBfsTimeBudget (update u)) <=
          Finset.univ.sum (fun _u : U => 2 * Fintype.card Y ^ 2) := by
            apply Finset.sum_le_sum
            intro u _
            exact (reverse_bfs_correct_and_quadratic
              (update u) (fun _ : Y => ())).2.1
      _ = Fintype.card U * (2 * Fintype.card Y ^ 2) := by simp
      _ = 2 * Fintype.card U * Fintype.card Y ^ 2 := by ac_rfl
  · unfold controlledSpaceBudget
    calc
      Finset.univ.sum (fun u => reverseBfsSpaceBudget (update u)) <=
          Finset.univ.sum (fun _u : U => 3 * Fintype.card Y ^ 2) := by
            apply Finset.sum_le_sum
            intro u _
            exact (reverse_bfs_correct_and_quadratic
              (update u) (fun _ : Y => ())).2.2
      _ = Fintype.card U * (3 * Fintype.card Y ^ 2) := by simp
      _ = 3 * Fintype.card U * Fintype.card Y ^ 2 := by ac_rfl

-- A two-input, two-state controlled system witnesses a nontrivial domain.
example :
    controlledTimeBudget (fun _ : Bool => not) <=
        2 * Fintype.card Bool * Fintype.card Bool ^ 2 /\
      controlledSpaceBudget (fun _ : Bool => not) <=
        3 * Fintype.card Bool * Fintype.card Bool ^ 2 := by
  exact controlled_pair_edge_complexity fun _ : Bool => not

#print axioms controlled_pair_edge_complexity

end D5.S3.ObserverMemory.Algorithms.ControlledPairEdgeComplexity
