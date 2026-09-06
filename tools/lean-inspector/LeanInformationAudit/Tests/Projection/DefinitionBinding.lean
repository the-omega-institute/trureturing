import LeanInformationAudit.Tests.Projection.V3Seal

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/--
info: layer-definition rejected IE-C042 KernelProjectionCertificateMismatch root=LeanInformationAudit.Tests.Projection.V3Seal catalog=importedBool component=definition:LayerDefinitionBinding.canonical.layers.kernel_1 expected=retained-value actual=different
node-definition rejected IE-C042 KernelProjectionCertificateMismatch root=LeanInformationAudit.Tests.Projection.V3Seal catalog=importedBool component=definition:NodeDefinitionBinding.K_ expected=retained-value actual=different
-/
#guard_msgs in
run_cmd do
  let root := `LeanInformationAudit.Tests.Projection.V3Seal
  let some counts := (SealRecords.forRoot (← getEnv) root)[0]?
    | throwError "missing sealed fixture"
  let mut messages := #[]
  for (label, certPrefix, layer) in #[("layer-definition", `LayerDefinitionBinding, true),
      ("node-definition", `NodeDefinitionBinding, false)] do
    let ((projection, analysis, layers), declarations) ← liftTermElabM do
      (prepareKernelProjection (← mkConstWithFreshMVarLevels counts.catalog.catalogName)
        (← mkConstWithFreshMVarLevels counts.catalog.arenaName)
        (counts.theorems.map (·.unitName)) root counts.catalog.catalogId
        counts.catalog.arenaName certPrefix).run #[]
    let target := if layer then layers[0]!.kernels.back! else certPrefix.str "K_"
    let source := if layer then layers[0]!.kernels[0]! else certPrefix.str "K_0"
    let some (.defnDecl replacement) := declarations.find? (·.getNames.contains source)
      | throwError "missing replacement definition {source}"
    for declaration in declarations do
      let declaration := match declaration with
        | .defnDecl info => if info.name == target then
            .defnDecl { info with value := replacement.value } else declaration
        | _ => declaration
      liftCoreM <| addDecl declaration
    unless ← liftTermElabM <| isDefEq (mkConst source) (mkConst target) do
      throwError "definition mutation did not reach the staged environment"
    let record : V3CatalogRecord := { counts, projection, analysis, layerChains := layers }
    let result ← try
      let _ ← liftTermElabM <| serializeV3Artifact root #[record]
        (root.str "__system_catalog_irredundant")
      pure "ACCEPTED"
    catch error => pure ("rejected " ++ (← error.toMessageData.toString))
    messages := messages.push (label ++ " " ++ result)
  logInfo (String.intercalate "\n" messages.toList)
