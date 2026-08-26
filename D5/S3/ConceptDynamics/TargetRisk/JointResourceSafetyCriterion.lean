/- GID: D5/S3/ConceptDynamics/TargetRisk/JointResourceSafetyCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TargetRisk/JointResourceSafetyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Jointly attainable caps characterize safety by their total recoverable budget. -/

import Mathlib

/- Library-search audit trail (2026-08-26):
   * Repository searches by theorem name, atom fingerprint, resource-stock
     recurrence, cap sums, and body shape found no exact theorem or canonical
     stock/recovery/extraction definition.
   * `TermBoundDoesNotBoundFamilySum` is an analogous finite-sum warning, but
     does not state the resource-safety criterion or its jointly unsafe witness.
   * Mathlib has no exact theorem for the full statement. The reverse direction
     directly applies `Finset.sum_le_sum` to the local cap inequalities.
   * `loogle` and `leansearch` are unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.ConceptDynamics.TargetRisk.JointResourceSafetyCriterion

/-- When the vector of local extraction caps is itself feasible, the caps
guarantee the minimum next-period stock exactly when their sum fits inside the
stock-plus-recovery budget. Two agents extracting three quarters each witness
that individual safety checks do not imply joint safety. -/
theorem jointly_attainable_caps_characterize_resource_safety :
    (forall {Agent : Type*} [Fintype Agent]
        (stock minimumStock : Real) (recovery : Real -> Real)
        (cap : Agent -> Real) (feasible : (Agent -> Real) -> Prop),
      feasible cap ->
      (forall extraction, feasible extraction ->
        forall i, 0 <= extraction i ∧ extraction i <= cap i) ->
      ((forall extraction, feasible extraction ->
          minimumStock <= stock + recovery stock - ∑ i, extraction i) <->
        ∑ i, cap i <= stock + recovery stock - minimumStock)) ∧
    (exists (stock minimumStock : Real) (recovery : Real -> Real)
        (cap extraction : Fin 2 -> Real),
      stock = 1 ∧
      minimumStock = 0 ∧
      recovery = (fun _ => 0) ∧
      cap = (fun _ => (3 / 4 : Real)) ∧
      extraction = cap ∧
      (forall i, 0 <= extraction i ∧ extraction i <= cap i) ∧
      (forall i,
        minimumStock <= stock + recovery stock - extraction i) ∧
      stock + recovery stock - ∑ i, extraction i < minimumStock) := by
  constructor
  · intro Agent _ stock minimumStock recovery cap feasible capFeasible boundedByCap
    constructor
    · intro guaranteesSafety
      have capSafety := guaranteesSafety cap capFeasible
      linarith
    · intro capSumFits extraction extractionFeasible
      have extractionSumLeCapSum :
          ∑ i, extraction i <= ∑ i, cap i := by
        exact Finset.sum_le_sum fun i _ =>
          (boundedByCap extraction extractionFeasible i).2
      linarith
  · refine ⟨1, 0, (fun _ => 0), (fun _ => (3 / 4 : Real)),
      (fun _ => (3 / 4 : Real)), ?_⟩
    norm_num [Fin.sum_univ_two]

#print axioms jointly_attainable_caps_characterize_resource_safety

end D5.S3.ConceptDynamics.TargetRisk.JointResourceSafetyCriterion
