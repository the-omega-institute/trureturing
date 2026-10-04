import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog
import LeanInformationAudit.Contract.Assessment

namespace LeanInformationAuditRegTests.ContractCatalogIndependence
open Lean Meta Elab Command LeanInformationAudit LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

private def registrationOwner : Name :=
  `LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
private def catalogOwner : Name :=
  `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog

/-- Separate compiler import closures retain the identical registration owner. -/
private unsafe def layout (withCatalog : Bool) : IO (Json × Nat × Nat) := do
  enableInitializersExecution
  let root := if withCatalog then catalogOwner else registrationOwner
  let search ← searchPathRef.get
  let testArtifacts := (← Repository.root) / ".lake/build/lean-inspector/reg/lib/lean"
  let env ← try
    searchPathRef.set (testArtifacts :: search)
    importModules #[{ module := root }, { module := `LeanInformationAudit.Registry }]
      {} (trustLevel := 0) (loadExts := true)
  finally searchPathRef.set search
  let action : MetaM (Json × Nat × Nat) := do
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
    return (wire, snapshot.roots.size, owners.size)
  let ((value, _), _) ← action.run.toIO
    { fileName := "<catalog control>", fileMap := default } { env := env.setExporting false }
  return value

run_meta do
  let (present, presentRoots, presentModules) ← layout true
  let (absent, absentRoots, absentModules) ← layout false
  let fields := (present.getObj?.toOption.map (·.toArray.map Prod.fst)).getD #[]
  let differences := fields.filter fun field =>
    (present.getObjVal? field).toOption != (absent.getObjVal? field).toOption
  for field in fields do
    assertTest s!"catalog.independence.{field}" (!differences.contains field)
  assertTest "catalog.independence.complete_record" (present == absent && fields.size == 12)
  assertTest "catalog.independence.layout" (presentRoots == 1 && absentRoots == 0 &&
    presentModules == absentModules + 1)
  logInfo m!"CATALOG_INDEPENDENCE {Json.mkObj [
    ("present", present), ("absent", absent), ("differences", toJson differences),
    ("fields", toJson fields), ("present_roots", toJson presentRoots),
    ("absent_roots", toJson absentRoots), ("present_modules", toJson presentModules),
    ("absent_modules", toJson absentModules)] |>.compress}"
end LeanInformationAuditRegTests.ContractCatalogIndependence
