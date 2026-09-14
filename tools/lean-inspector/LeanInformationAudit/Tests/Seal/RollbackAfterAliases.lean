import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
open Lean Lean.Elab.Command LeanInformationAudit LeanInformationAudit.Tests.ImportClosureProducer
expect_information_occurrence importedTheorem in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"
run_cmd do
  let env ← getEnv
  let root := env.header.mainModule
  let arena := ``objectArena
  let member := ``importedTheorem
  let collision := catalogQualifiedName root arena `importedBool arena "__information_catalog"
  elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ collision)) : True := True.intro))
  let before ← getEnv
  let mut rejected := false
  try prepareSealPublication
  catch error => rejected := (← error.toMessageData.toString).startsWith "IE-C025"
  let mut exportRejected := false
  try discard <| prepareInformationAnalysisExport root [.seal, .analysis, .ascii]
  catch _ => exportRejected := true
  let after ← getEnv
  let generated := #[theoremUnitSuffix, primitiveRealizationSuffix, "__lowers_escape",
    "__escape_enriched"].map (catalogQualifiedName root arena `importedBool member)
  unless rejected && exportRejected && !(generated.any after.contains) &&
      (SealRecords.forRoot after root).isEmpty && (SealRecords.analysisForRoot? after root).isNone &&
      (← mkModuleData after).constants.size == (← mkModuleData before).constants.size do
    throwError "RollbackAfterAliases: leaked declarations or retained artifacts"
