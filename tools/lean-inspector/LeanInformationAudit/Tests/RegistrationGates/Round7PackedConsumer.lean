import LeanInformationAuditAnalysis.Tests.Round7PackedCarrier
import LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries
import LeanInformationAudit.StructuralRealization
open Lean LeanInformationAudit.RegistrationGates
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  for (label, readout) in [("PackedCarrierHidden", ``Round7PackedCarrier.hidden),
      ("PackedCarrierOpaqueClean", ``Round7PackedCarrier.clean)] do
    let result ← readoutClosure env ``AllowlistBoundaries.target (mkConst readout)
    -- Both external values have the same insufficient type evidence. It is
    -- acceptable to reject both fail-closed until this representation is supported.
    if result.1 && result.2.isSome then logInfo m!"[PASS] {label}: {result}"
    else logError m!"[FAIL] {label}: expected completed rejection; actual={result}"

namespace Round7PackedConsumer
open LeanInformationAudit D5.S3.ConceptDynamics.InformationEscape
def signature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => Round7PackedCarrier.Packet
def hidden : StructuralPrimitiveRealization ⟨Bool⟩ signature := ⟨Round7PackedCarrier.hidden⟩
def clean : StructuralPrimitiveRealization ⟨Bool⟩ signature := ⟨Round7PackedCarrier.clean⟩
def plain : PrimitiveRealization AllowlistBoundaries.signature := ⟨Round7PackedCarrier.plain, Fin.elim0⟩
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let mut classes : Std.HashMap Name Bool := {}
  for index in [:env.header.modules.size] do
    let name := env.header.modules[index]!.module
    let inherited := match env.header.moduleData[index]? with
      | none => true
      | some data => data.imports.any (fun i => classes[i.module]?.getD true)
    classes := classes.insert name
      (name.getRoot == `D5 || name.getRoot == `LeanInformationAudit || inherited)
  let some idx := env.getModuleIdxFor? ``Round7PackedCarrier.hidden
    | throwError "[INVALID] missing external metadata"
  let moduleName := env.header.modules[idx.toNat]!.module
  let isProtected := classes[moduleName]?.getD true
  logInfo m!"[METADATA] module={moduleName} protected={isProtected} imports={env.header.moduleData[idx.toNat]!.imports.map (·.module)}"
  if isProtected then throwError "[INVALID] external module is protected"
  for (label, holder) in [("PackedCarrierHidden", ``hidden),
      ("PackedCarrierOpaqueClean", ``clean), ("ExternalBoolPositive", ``plain)] do
    let actual ← provenanceErrorCurrent env.header.mainModule `catalog ``AllowlistBoundaries.target holder
    let expected := if label == "ExternalBoolPositive" then actual.isNone else
      actual.any (fun message => message.startsWith "IE-C050 ClosedTruthReadout " &&
        (message.contains "reason=unclassified_form" || message.contains "reason=forbidden_dependency"))
    if expected then logInfo m!"[PASS] {label}Diagnostic: {actual}"
    else logError m!"[FAIL] {label}Diagnostic: {actual}"
  let actual ← readoutClosure env ``AllowlistBoundaries.target (mkConst ``Round7PackedCarrier.plain)
  if !actual.1 && actual.2.isSome then logInfo m!"[PASS] ExternalBoolPositive: {actual}"
  else logError m!"[FAIL] ExternalBoolPositive: {actual}"
end Round7PackedConsumer
