import Reg.Catalogs.InformationRoot
import Reg.Catalogs.SharedInformationRoot
import Reg.Catalogs.TemplateShadow
import LeanInformationAuditRegTests.ProductionInputs
import LeanInformationAudit.Tests.Seal.M3
import LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership

open Lean Lean.Elab.Command LeanInformationAudit
open Reg.Support

-- Inspect diagnostics in the actual producer, including after one old root is
-- split among several leaves. Expected counts come only from content contracts.
private def checkDiagnostics (root : Name) (expected : Nat) : CommandElabM Nat := do
  let env := (← getEnv).setExporting false
  let some idx := env.getModuleIdx? root
    | throwError "[FAIL] FrozenRootsCompile: module not loaded: {root}"
  let mut checked : Nat := 0
  let mut findings : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    unless name.getString! == "__information_registration_diagnostic" do continue
    let some (.defnInfo info) := env.find? name
      | throwError "[FAIL] FrozenRootsCompile: missing metadata: {name}"
    let .lit (.strVal message) := info.value
      | throwError "[FAIL] FrozenRootsCompile: malformed metadata: {name}"
    checked := checked + 1
    if message.startsWith "IE-C050 " then
      findings := findings + 1
      logInfo m!"{message}"
  logInfo m!"FrozenRootsCompile root={root} registrations={checked} IE-C050={findings}"
  unless checked == expected do
    throwError "[FAIL] FrozenRootMetadataCount: {root}: {checked} != {expected}"
  unless findings == 0 do
    throwError "[FAIL] FrozenRootsCompile: {findings} IE-C050 findings"
  return checked

run_cmd do
  let families := #[(InformationRootContract.contract.expected, 11),
    (TemplateShadowContract.contract.expected, 10),
    (SharedInformationRootContract.causalOccurrences, 2)]
  let mut productionTotal := 0
  for (rows, expected) in families do
    unless rows.size == expected && expected > 0 do
      throwError "[FAIL] FrozenRootsCompile: independent production family count"
    discard <| liftCoreM <| LeanInformationAuditRegTests.productionEntries rows
    let owners := (rows.map (·.registrationModuleName)).toList.eraseDups
    let mut checked := 0
    for owner in owners do
      let count := (rows.filter (·.registrationModuleName == owner)).size
      unless count > 0 do throwError "[FAIL] FrozenRootsCompile: empty producer group"
      checked := checked + (← checkDiagnostics owner count)
    unless checked == expected do throwError "[FAIL] FrozenRootsCompile: production family total"
    productionTotal := productionTotal + checked
  unless productionTotal == 23 do throwError "[FAIL] FrozenRootsCompile: production total"
  -- A catalog has no registrations of its own. These zeros do not replace the
  -- positive producer checks above; the original SharedInformationRoot role stays zero.
  for root in #[InformationRootContract.rootId, SharedInformationRootContract.rootId,
      TemplateShadowContract.rootId] do
    discard <| checkDiagnostics root 0
  let synthetic ← checkDiagnostics `LeanInformationAudit.Tests.Seal.M3 7
  unless productionTotal + synthetic == 30 do throwError "[FAIL] FrozenRootsCompile: total"
  logInfo "[PASS] FrozenRootsCompile: production=23 synthetic=7 catalogs=0 findings=0"

-- Keep all eleven production ownership assertions and both wrong-owner controls.
run_meta do
  let expected := InformationRootContract.contract.expected
  unless expected.size == 11 do throwError "expected eleven production owner controls"
  for owner in (expected.map (·.registrationModuleName)).toList.eraseDups do
    let count := (expected.filter (·.registrationModuleName == owner)).size
    LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership.checkImportedOwners owner count
