import LeanInformationAuditInterface.Syntax
import LeanInformationAudit.Tests.CohortArena

/-! Report target of `CohortIndependence`, compiled as a `Reg` module is. It
enrolls `cutRealization` itself and registers one occurrence through it, and a
second occurrence through `iffRealization`, which nothing it imports enrolls. -/

namespace LeanInformationAudit.Tests.CohortTarget
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates IffRegistrationTemplates
open LeanInformationAudit.Tests.CohortArena

local instance : DecidableEq arena.State := instDecidableEqBool

theorem statement : ∀ x : Bool, x = x := fun _ => rfl
theorem legacy : LegacyPrimitiveRealization arena (∀ x : Bool, x = x) reads :=
  ⟨⟨fun _ => rfl, fun _ => statement⟩⟩
theorem unenrolled : ∀ x : Bool, x = x := fun _ => rfl
theorem unenrolledLegacy : LegacyPrimitiveRealization arena (∀ x : Bool, x = x) reads :=
  ⟨⟨fun _ => rfl, fun _ => unenrolled⟩⟩

register_information_template cutRealization

register_information_theorem statement in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives reads.toPrimitiveBundle realization legacy
  variation lawVariation sensitivity slotSensitivity
  escape from (Bool) escape continues (open)

register_information_theorem unenrolled in arena
  readout via (@iffRealization Bool (fun x => x) (fun x => x))
  primitives reads.toPrimitiveBundle realization unenrolledLegacy
  variation lawVariation sensitivity slotSensitivity
  escape from (Bool) escape continues (open)

end LeanInformationAudit.Tests.CohortTarget
