import LeanInformationAudit.SealCommand

open Lean Elab Command

namespace LeanInformationAudit.Tests.InterfaceGrammarDispatch

/-- Parse through the imported grammar, check the actual command-elaborator table,
and execute the handler. Missing names deliberately reach its first semantic gate.
The state is restored after each case, including any seal publication. -/
private def checkDispatch (source kind diagnostic : String) : CommandElabM Unit := do
  let env ← getEnv
  let stx ← ofExcept <| Parser.runParserCategory env `command source
  let expected := Name.str `LeanInformationAudit kind
  unless stx.getKind == expected do
    throwError "grammar kind changed: {stx.getKind}, expected {expected}"
  let some owner := env.getModuleIdxFor? stx.getKind
    | throwError "grammar owner missing: {stx.getKind}"
  unless env.allImportedModuleNames[owner.toNat]! == `LeanInformationAuditInterface.Syntax do
    throwError "grammar is not owned by Interface: {stx.getKind}"
  let handlers := commandElabAttribute.getEntries env stx.getKind
  let [handler] := handlers
    | throwError "expected one implementation handler: {stx.getKind}, got {handlers.length}"
  let some handlerOwner := env.getModuleIdxFor? handler.declName
    | throwError "handler owner missing: {stx.getKind}"
  let implementation := env.allImportedModuleNames[handlerOwner.toNat]!
  unless implementation == `LeanInformationAudit.Syntax ||
      implementation == `LeanInformationAudit.SealCommand do
    throwError "unexpected handler owner: {implementation}"
  let saved ← get
  modify fun state => { state with messages := {} }
  let failure ← try
    elabCommand stx
    pure ""
  catch error => error.toMessageData.toString
  let messages ← (← get).messages.toList.mapM fun message => message.data.toString
  set saved
  unless diagnostic.isEmpty || (failure :: messages).any (·.contains diagnostic) do
    throwError "handler diagnostic missing for {stx.getKind}: {failure :: messages}"

run_cmd do
  checkDispatch
    "expect_information_occurrence missingTheorem in missingArena from \"Owner\""
    "command___In__From_" "IE-C001"
  checkDispatch
    "expect_information_occurrence missingTheorem in missingArena from \"Owner\" statement_id \"identity\""
    "command___In__From__Statement_id_" "IE-C001"
  checkDispatch
    "register_information_template missingTemplate"
    "command__" "Unknown constant"
  checkDispatch
    "register_information_template missingTemplate constructors 1 [Nat]"
    "command__Constructors_[_,,]" "Unknown constant"
  checkDispatch
    "information_theorem probe in missingArena primitives p : True := by trivial"
    "informationTheoremCmd" "IE-C003"
  checkDispatch
    "register_information_theorem missingTheorem in missingArena primitives p realization r"
    "registerInformationTheoremCmd" "IE-C001"
  checkDispatch
    "register_information_theorem missingTheorem via descriptor in missingArena"
    "registerInformationTheoremViaCmd" "IE-C003"
  checkDispatch
    "information_theorem probe in missingArena object_arena obj catalog cat primitives p : True := by trivial"
    "informationTheoremOccurrenceCmd" "IE-C003"
  checkDispatch
    "register_information_theorem missingTheorem in missingArena object_arena obj catalog cat primitives p realization r"
    "registerInformationTheoremOccurrenceCmd" "IE-C001"
  checkDispatch
    "register_information_theorem missingTheorem in missingArena readout via (descriptor) primitives p realization r"
    "registerInformationTheoremReadoutCmd" "IE-C003"
  checkDispatch
    "register_information_theorem missingTheorem via descriptor in missingArena readout via (descriptor)"
    "registerInformationTheoremViaReadoutCmd" "IE-C003"
  checkDispatch
    "register_information_theorem missingTheorem in missingArena object_arena obj catalog cat readout via (descriptor) primitives p realization r"
    "registerInformationTheoremOccurrenceReadoutCmd" "IE-C003"
  checkDispatch
    "information_theorem probe in missingArena readout via (descriptor) primitives p : True := by trivial"
    "informationTheoremReadoutCmd" "IE-C003"
  checkDispatch
    "information_theorem probe in missingArena object_arena obj catalog cat readout via (descriptor) primitives p : True := by trivial"
    "informationTheoremOccurrenceReadoutCmd" "IE-C003"
  checkDispatch
    "declare_information_template_binding missingTheorem in missingArena readout via (descriptor)"
    "declareInformationTemplateBindingCmd" "IE-C003"
  checkDispatch
    "#seal_information_theory"
    "sealInformationTheoryCmd" ""
  checkDispatch
    "#stage_information_analysis root missingRoot"
    "stageInformationAnalysisCmd" "UnsealedAnalysisStage"
  checkDispatch
    "#export_information_analysis root missingRoot"
    "exportInformationAnalysisCmd" "UnstagedAnalysisExport"

end LeanInformationAudit.Tests.InterfaceGrammarDispatch
