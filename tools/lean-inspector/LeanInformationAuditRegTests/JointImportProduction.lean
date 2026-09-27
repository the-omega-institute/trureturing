import Reg.Catalogs.InformationRoot
import Reg.Catalogs.TemplateShadow
import LeanInformationAuditRegTests.ProductionInputs

open Lean LeanInformationAudit

/-! Exercise the production pair that a full report imports into one environment. -/
run_cmd do
  let env ← getEnv
  let roots := #[(Reg.Support.InformationRootContract.contract, 11,
      Reg.Support.InformationRootContract.expectedSealDigest),
    (Reg.Support.TemplateShadowContract.contract, 10,
      Reg.Support.TemplateShadowContract.expectedSealDigest)]
  for (contract, expected, digest) in roots do
    let root := contract.rootId
    unless contract.expected.size == expected do throwError "independent production count changed"
    discard <| Lean.Elab.Command.liftCoreM <|
      LeanInformationAuditRegTests.productionEntries contract.expected
    let records := SealRecords.forRoot env root
    unless records.size == expected && SealRecords.systemCatalogIrredundant env root do
      throwError "production joint import lost sealed catalogs: {root}"
    for record in records do
      for name in #[record.catalog.catalogName, record.verdict.name] ++
          record.theorems.flatMap (fun row =>
            #[row.unitName, row.realizationName, row.certificateName]) do
        unless (env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!) == some root do
          throwError "production companion has the wrong module owner: {name}"
    let artifact ← Lean.Elab.Command.liftTermElabM <| serializeSealArtifact records
    unless Sha256.hex artifact.toUTF8 == digest do
      throwError "production joint seal digest mismatch: {root}"
  logInfo "production joint import retained eleven frozen and ten shadow catalogs"
