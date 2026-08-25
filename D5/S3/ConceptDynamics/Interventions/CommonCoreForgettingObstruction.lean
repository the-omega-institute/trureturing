/- GID: D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nontrivial safety-blame core prevents safety-preserving complete blame erasure. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-22):
   * Exact repository hits `Concept` and `Refines` are the canonical source
     readout carrier and factorization order; both are imported directly.
   * Repository searches for common concept factors, kernel joins, and complete
     forgetting found no theorem stating this obstruction.
   * The adjacent `ObserverMemory.Fusion.CommonPredictionFactor` constructs a
     dynamics-stable common quotient, but its extra update semantics do not
     subsume this static concept theorem.
   * Exact pinned-Mathlib hits `Setoid.completeLattice`, `sup_le_sup`, and
     `top_unique` construct the common-core relation and close its monotonicity
     argument; all are applied below.
   * `loogle` and `leansearch` executables were absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.CommonCoreForgettingObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- The common core of two concepts is the least equivalence relation containing
both readout kernels. Its quotient is their greatest common coarsening. -/
def commonCoreRelation {X SafetyInfo BlameInfo : Type*}
    (safety : Concept X SafetyInfo) (blame : Concept X BlameInfo) : Setoid X :=
  Setoid.ker safety ⊔ Setoid.ker blame

/-- If safety and blame have a nontrivial common core, a future concept cannot
both retain all safety information and have only the trivial common core with
blame. -/
theorem common_core_obstructs_complete_forgetting
    {X SafetyInfo BlameInfo FutureInfo : Type*}
    (safety : Concept X SafetyInfo) (blame : Concept X BlameInfo)
    (future : Concept X FutureInfo)
    (commonCoreNontrivial : commonCoreRelation safety blame ≠ ⊤) :
    ¬(Refines safety future ∧ commonCoreRelation future blame = ⊤) := by
  rintro ⟨⟨safetyFactor, safetyFactors⟩, completeErasure⟩
  apply commonCoreNontrivial
  apply top_unique
  rw [← completeErasure]
  apply sup_le_sup
  · intro left right futureEqual
    calc
      safety left = safetyFactor (future left) := congrFun safetyFactors left
      _ = safetyFactor (future right) := congrArg safetyFactor futureEqual
      _ = safety right := (congrFun safetyFactors right).symm
  · exact le_rfl

/-- The nontrivial-core premise and the safety-preservation clause are jointly
satisfiable for identity readouts on a two-state space. -/
example :
    commonCoreRelation (id : Concept Bool Bool) (id : Concept Bool Bool) ≠ ⊤ ∧
      Refines (id : Concept Bool Bool) (id : Concept Bool Bool) := by
  constructor
  · intro coreTrivial
    have falseEqualsTrue :
        commonCoreRelation (id : Concept Bool Bool) (id : Concept Bool Bool)
          false true := by
      rw [coreTrivial]
      trivial
    unfold commonCoreRelation at falseEqualsTrue
    rw [sup_idem] at falseEqualsTrue
    exact Bool.false_ne_true falseEqualsTrue
  · exact ⟨id, rfl⟩

#print axioms common_core_obstructs_complete_forgetting

end D5.S3.ConceptDynamics.Interventions.CommonCoreForgettingObstruction
