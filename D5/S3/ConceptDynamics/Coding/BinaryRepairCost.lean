/- GID: D5/S3/ConceptDynamics/Coding/BinaryRepairCost
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BinaryRepairCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary repair needs exactly the ceiling binary logarithm of minimal labels. -/

import D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'binary_repair_cost_is_log_of_minimal_labels'
     D5 Golden/Frozen/accepted` returned no matches.
   * `rg -n 'clog|log2|Nat.log|binary.*cost|label' D5/ --glob '*.lean'`
     found `FiberBinaryIdentification`, which uses `Nat.le_pow_clog` for a
     sufficient logarithmic-depth protocol but has no matching lower bound.
   * `MinimalAppealLabelCount.minimal_appeal_label_count` is the exact upstream
     minimum-label theorem; this module transports its construction and lower
     bound across the finite type of `k`-bit Boolean strings instead of
     reproving either fiber-counting direction.
   * The pinned-Mathlib search found `Fintype.equivFinOfCardEq`, function-type
     cardinality simplification, `Nat.le_pow_clog`, and the exact Galois law
     `Nat.clog_le_iff_le_pow`. These are the only coding and arithmetic machines
     used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.BinaryRepairCost

open D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

/-- A fixed-width binary auxiliary label makes the target exact when equal
records and equal bit strings force equal target outcomes. -/
def BinaryLabelDetermines {X C Target : Type*} {k : Nat}
    (record : X -> C) (target : X -> Target)
    (label : X -> Fin k -> Bool) : Prop :=
  forall x y, record x = record y -> label x = label y -> target x = target y

/-- A width is feasible when some fixed-width binary auxiliary label makes the
target exact relative to the original record. -/
def BinaryRepairFeasible {X C Target : Type*}
    (record : X -> C) (target : X -> Target) (k : Nat) : Prop :=
  exists label : X -> Fin k -> Bool, BinaryLabelDetermines record target label

/-- Binary repair is feasible exactly when its bit strings cover the upstream
minimal label count, and the ceiling binary logarithm is the least feasible width. -/
theorem binary_repair_cost_is_log_of_minimal_labels
    {X C Target : Type*} [Fintype X] [Fintype C]
    (record : X -> C) (target : X -> Target) :
    (forall k, BinaryRepairFeasible record target k <->
      worstFiberDiversity record target <= 2 ^ k) /\
    IsLeast {k | BinaryRepairFeasible record target k}
      (Nat.clog 2 (worstFiberDiversity record target)) := by
  classical
  rcases minimal_appeal_label_count record target with
    ⟨⟨minimalLabel, minimalLabelDetermines⟩, labelLowerBound⟩
  have feasible_iff (k : Nat) :
      BinaryRepairFeasible record target k <->
        worstFiberDiversity record target <= 2 ^ k := by
    let bitEquiv : (Fin k -> Bool) ≃ Fin (2 ^ k) :=
      Fintype.equivFinOfCardEq (by simp)
    constructor
    · rintro ⟨binaryLabel, binaryLabelDetermines⟩
      let finiteLabel : X -> Fin (2 ^ k) := fun x => bitEquiv (binaryLabel x)
      apply labelLowerBound finiteLabel
      intro x y sameRecord sameFiniteLabel
      apply binaryLabelDetermines x y sameRecord
      exact bitEquiv.injective sameFiniteLabel
    · intro enoughCodes
      let binaryLabel : X -> Fin k -> Bool := fun x =>
        bitEquiv.symm (Fin.castLE enoughCodes (minimalLabel x))
      refine ⟨binaryLabel, ?_⟩
      intro x y sameRecord sameBinaryLabel
      apply minimalLabelDetermines x y sameRecord
      apply Fin.castLE_injective enoughCodes
      exact bitEquiv.symm.injective sameBinaryLabel
  refine ⟨feasible_iff, ?_⟩
  constructor
  · exact (feasible_iff _).2
      (Nat.le_pow_clog (b := 2) (by decide) (worstFiberDiversity record target))
  · intro k feasible
    exact (Nat.clog_le_iff_le_pow (by decide)).2 ((feasible_iff k).1 feasible)

example :
    (forall k, BinaryRepairFeasible (fun _ : Bool => ()) id k <-> 2 <= 2 ^ k) /\
    IsLeast {k | BinaryRepairFeasible (fun _ : Bool => ()) id k} 1 := by
  have diversity_is_two :
      worstFiberDiversity (fun _ : Bool => ()) (id : Bool -> Bool) = 2 := by
    simp [worstFiberDiversity, fiberTargetDiversity, fiberTargetValues]
  have clog_two_is_one : Nat.clog 2 2 = 1 := by decide
  simpa only [diversity_is_two, clog_two_is_one] using
    binary_repair_cost_is_log_of_minimal_labels (fun _ : Bool => ()) id

#print axioms binary_repair_cost_is_log_of_minimal_labels

end D5.S3.ConceptDynamics.Coding.BinaryRepairCost
