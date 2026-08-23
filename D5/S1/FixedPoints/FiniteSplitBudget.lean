/- GID: D5/S1/FixedPoints/FiniteSplitBudget
   generality: G
   mirror-B: D5/B/S1/FixedPoints/FiniteSplitBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite partitions admit only the initial class-count deficit many strict splits. -/

/- Library-search audit trail (2026-08-23):
   * The exact repository theorem
     `D5.S1.FixedPoints.FiniteRepairTermination.finite_strict_repairs_stabilize`
     already proves the sharp strict-change bound for a monotone sequence of finite equivalence
     partitions; it is imported and applied directly below.
   * Pinned Mathlib search found `Finpartition.card_mono` and
     `Finpartition.card_parts_le_card` in `Mathlib/Order/Partition/Finpartition.lean`, and
     `Set.ncard_Ioc_nat` in `Mathlib/Order/Interval/Set/Nat.lean`.
   * No pinned-Mathlib declaration directly packages the strict-change count with the sharp
     difference between the carrier cardinality and the initial number of parts. -/

import D5.S1.FixedPoints.FiniteRepairTermination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.FixedPoints.FiniteSplitBudget

open Finset
open D5.S1.FixedPoints.FiniteRepairTermination

/-- A refinement sequence of equivalence partitions of a finite carrier has at most the carrier
cardinality minus the initial number of equivalence classes many strict changes. -/
theorem strict_refinement_count_le_card_sub_initial_classes
    {X : Type*} [Fintype X] [DecidableEq X]
    (partition : ℕ → Finpartition (Finset.univ : Finset X))
    (refines : ∀ n : ℕ, partition (n + 1) ≤ partition n) :
    {n : ℕ | partition (n + 1) ≠ partition n}.ncard ≤
      Fintype.card X - #(partition 0).parts :=
  (finite_strict_repairs_stabilize partition refines).2

#print axioms strict_refinement_count_le_card_sub_initial_classes

end D5.S1.FixedPoints.FiniteSplitBudget
