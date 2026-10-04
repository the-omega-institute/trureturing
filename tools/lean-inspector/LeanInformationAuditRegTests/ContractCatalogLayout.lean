import LeanInformationAuditRegTests.ContractControl
import LeanInformationAudit.Contract.Assessment

namespace LeanInformationAuditRegTests.ContractCatalogLayout
open Lean Meta Elab Command LeanInformationAudit LeanInformationAudit.Contract

private def registrationOwner : Name :=
  `LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
private def catalogOwner : Name :=
  `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog

/-- Assess one catalog layout without loading a second compiler environment. -/
def snapshot (withCatalog : Bool) : MetaM Json := do
  let env ← getEnv
  let root := if withCatalog then catalogOwner else registrationOwner
  let owners := env.header.moduleNames.filter fun name =>
    name == registrationOwner || name == catalogOwner || (`Reg).isPrefixOf name
  let requirements ← RootStructure.requiredFor owners Discovery.moduleSource
  let snapshot ← Discovery.discoverWithStructure requirements owners
  let snapshot := { snapshot with registrations := snapshot.registrations.filter (·.1 == registrationOwner) }
  unless snapshot.registrations.size == 1 do throwError "control:registration_count"
  unless snapshot.roots.size == (if withCatalog then 1 else 0) do
    throwError "control:catalog_count"
  if withCatalog then
    unless snapshot.roots[0]!.2.expected.any
        (·.registrationModuleName == registrationOwner) do throwError "control:membership"
  TypedAssessment.assessSnapshot snapshot
  let input ← RegistrationAssessmentInput.capture root
  let rows ← TemplateBinding.assessJoined input
  unless rows.size == 1 do throwError "control:assessment_count:{rows.size}"
  let wire ← TemplateBinding.recordJson rows[0]!
  return Json.mkObj [
    ("record", wire), ("roots", toJson snapshot.roots.size), ("modules", toJson owners.size)]

end LeanInformationAuditRegTests.ContractCatalogLayout
