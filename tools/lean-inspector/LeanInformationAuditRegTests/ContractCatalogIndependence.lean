import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAuditRegTests.ContractCatalogPresent
import LeanInformationAuditRegTests.ContractCatalogAbsent

namespace LeanInformationAuditRegTests.ContractCatalogIndependence
open Lean Meta Elab Command
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let presentLayout ← ContractControl.read ContractCatalogPresent.result
  let absentLayout ← ContractControl.read ContractCatalogAbsent.result
  let present ← ofExcept <| presentLayout.getObjVal? "record"
  let absent ← ofExcept <| absentLayout.getObjVal? "record"
  let presentRoots ← ofExcept <| presentLayout.getObjValAs? Nat "roots"
  let absentRoots ← ofExcept <| absentLayout.getObjValAs? Nat "roots"
  let presentModules ← ofExcept <| presentLayout.getObjValAs? Nat "modules"
  let absentModules ← ofExcept <| absentLayout.getObjValAs? Nat "modules"
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
