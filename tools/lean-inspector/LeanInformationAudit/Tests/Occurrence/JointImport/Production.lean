import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

open Lean LeanInformationAudit

/-! Exercise the production pair that a full report imports into one environment. -/
run_cmd do
  let env ← getEnv
  let roots := #[(frozenInformationRootId, 11),
    (`D5.S3.ConceptDynamics.InformationEscape.TemplateShadow, 10)]
  for (root, expected) in roots do
    let records := SealRecords.forRoot env root
    unless records.size == expected && SealRecords.systemCatalogIrredundant env root do
      throwError "production joint import lost sealed catalogs: {root}"
    for record in records do
      for name in #[record.catalog.catalogName, record.irredundantCertificateName] ++
          record.theorems.flatMap (fun row => #[row.unitName, row.certificateName]) do
        unless (env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!) == some root do
          throwError "production companion has the wrong module owner: {name}"
  logInfo "production joint import retained eleven frozen and ten shadow catalogs"
