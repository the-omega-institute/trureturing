/- GID: D5/S3/ConceptDynamics/Audits/LedgerIntegrityVeracitySeparation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Audits/LedgerIntegrityVeracitySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An injective ledger can preserve systematically false reports. -/

import Mathlib.Logic.Equiv.Bool
import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-21):
   * Repository searches for injective ledgers, input veracity, report/event
     separation, and report encoding found no exact theorem. The nearby
     `equal_content_does_not_determine_admission` theorem concerns provenance
     rather than the source's report and true-event readouts.
   * Pinned Mathlib's exact `Bool.not_injective`, `Bool.not_ne_self`, and
     `Bool.not_ne_id` theorems supply the concrete witness facts and are applied
     directly below. `Bool.not_not` is an adjacent involution result but does
     not state the full ledger/veracity separation.
   * No exact pinned-Mathlib theorem packages all five public clauses. The
     `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.LedgerIntegrityVeracitySeparation

/-- There are true-event and report readouts and an injective report encoder
whose induced ledger exactly distinguishes reports, is itself injective, and
yet records a report opposite to the true event at every input. Thus ledger
integrity and input veracity have different truth values in this model. -/
theorem ledger_integrity_does_not_imply_input_veracity :
    ∃ (trueEvent report encode : Bool → Bool),
      Function.Injective encode ∧
      let ledger := encode ∘ report
      (∀ x y, ledger x ≠ ledger y ↔ report x ≠ report y) ∧
        (∀ x, report x ≠ trueEvent x) ∧
        Function.Injective ledger ∧
        ¬(Function.Injective ledger ↔ report = trueEvent) := by
  refine ⟨id, Bool.not, id, Function.injective_id, ?_⟩
  dsimp
  refine ⟨fun _ _ ↦ Iff.rfl, Bool.not_ne_self, Bool.not_injective, ?_⟩
  intro sameStatus
  exact Bool.not_ne_id (sameStatus.mp Bool.not_injective)

/-- Both values occur as inputs in the concrete source model. -/
example : Function.Surjective (id : Bool → Bool) := Function.surjective_id

#print axioms ledger_integrity_does_not_imply_input_veracity

end D5.S3.ConceptDynamics.Audits.LedgerIntegrityVeracitySeparation
