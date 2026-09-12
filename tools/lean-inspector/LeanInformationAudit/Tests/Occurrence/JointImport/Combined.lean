import LeanInformationAudit.Tests.Occurrence.JointImport.First
import LeanInformationAudit.Tests.Occurrence.JointImport.Second

open Lean LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.JointImport

/-! Separately compiled roots must retain their own catalogs for the same occurrence. -/
run_cmd do
  let env ← getEnv
  let roots := #[`LeanInformationAudit.Tests.Occurrence.JointImport.First,
    `LeanInformationAudit.Tests.Occurrence.JointImport.Second]
  unless (InformationRegistry.entries env).size == 2 do
    throwError "joint import lost source registrations"
  let mut generated : Array Name := #[]
  for root in roots do
    let records := SealRecords.forRoot env root
    unless records.size == 1 do throwError "joint import lost a catalog: {root}"
    let some record := records[0]? | throwError "missing catalog: {root}"
    unless record.catalog.arenaName == ``arena && record.catalog.units.size == 1 &&
        record.theorems.size == 1 && record.stateCard == 2 &&
        record.fullEscapeCount == 0 && SealRecords.systemCatalogIrredundant env root do
      throwError "joint import changed catalog evidence: {root}"
    let some occurrence := record.theorems[0]? | throwError "missing occurrence: {root}"
    unless occurrence.theoremName == ``shared && occurrence.registrationModuleName == root &&
        occurrence.uniqueCaptureCount == 2 && occurrence.withoutEscapeCount == 2 do
      throwError "joint import changed occurrence evidence: {root}"
    for name in #[record.catalog.catalogName, record.verdict.name,
        occurrence.unitName, occurrence.certificateName,
        occurrence.certificateName.getPrefix.str "__escape_enriched"] do
      unless (env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!) == some root do
        throwError "generated declaration has the wrong module owner: {name}"
      if generated.contains name then
        throwError "joint import merged generated declarations: {name}"
      generated := generated.push name
  logInfo "joint import retained both catalogs and their module-owned evidence"
