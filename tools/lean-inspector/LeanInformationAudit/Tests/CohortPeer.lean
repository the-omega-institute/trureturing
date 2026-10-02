import LeanInformationAuditInterface.Syntax
import LeanInformationAudit.Tests.CohortArena

/-! A peer that `CohortTarget` does not import. It enrolls both templates the
target names, `cutRealization` a second time and `iffRealization` the only
time, and registers its own occurrence. -/

namespace LeanInformationAudit.Tests.CohortPeer
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates IffRegistrationTemplates
open LeanInformationAudit.Tests.CohortArena

local instance : DecidableEq arena.State := instDecidableEqBool

theorem statement : ∀ x : Bool, x = x := fun _ => rfl
theorem legacy : LegacyPrimitiveRealization arena (∀ x : Bool, x = x) reads :=
  ⟨⟨fun _ => rfl, fun _ => statement⟩⟩

register_information_template iffRealization
register_information_template cutRealization

register_information_theorem statement in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives reads.toPrimitiveBundle realization legacy
  variation lawVariation sensitivity slotSensitivity
  escape from (Bool) escape continues (open)

end LeanInformationAudit.Tests.CohortPeer
