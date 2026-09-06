import LeanInformationAudit.SealCommand

/-!
The seal publication closure receives no syntax, destination, or artifact selector.
The later export closure receives only a root and artifact kinds, and cannot mutate
the environment. Destination strings are confined to the terminal IO writer.

The direct capability sets are pinned here. The seal may log, but cannot read
ambient syntax or files. The export may prepare bytes, but cannot publish or stage
declarations. RealSeal.lean exercises both audited closures against the production
commands and verifies rejection before any declaration or artifact escapes.
-/

open Lean Lean.Elab.Command LeanInformationAudit

example : CommandElabM Unit := @prepareSealPublication

example : Name -> CommandElabM Unit := @prepareInformationAnalysisStage

example : Name -> List ArtifactKind -> CommandElabM AnalysisExportPlan :=
  @prepareInformationAnalysisExport

#guard sealIOAllowlist == [``Lean.logInfo]

#guard sealSyntaxDenylist ==
  [``Lean.Elab.Command.getRef, ``MonadRef.getRef, ``withRef, ``MonadRef.withRef]

#guard leanCoreFileLoaderDenylist ==
  [``Lean.findOLean, ``Lean.readModuleData, ``Lean.readModuleDataParts,
    ``Lean.ModuleSetup.load]

#guard exportEnvironmentMutationDenylist.contains ``Lean.setEnv
#guard exportEnvironmentMutationDenylist.contains ``Lean.Elab.Command.elabCommand
#guard exportEnvironmentMutationDenylist.contains ``Lean.addAndCompile

-- Read elaborated dependency names so aliases cannot hide analysis work in seal.
run_cmd do
  let env ← getEnv
  let mut pending := #[``prepareSealPublication]
  let mut visited : Std.HashSet Name := {}
  let analysisNames := #[`LeanInformationAudit.prepareAnalysisProofs,
    `LeanInformationAudit.prepareInformationAnalysisStage,
    `LeanInformationAudit.retainAnalysisState]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if analysisNames.contains (privateToUserName name) then
      throwError "seal closure contains analysis staging: {privateToUserName name}"
    if let some info := env.find? name then
      let dependencies := match info with
        | .defnInfo info => info.value.getUsedConstants
        | .opaqueInfo info => info.value.getUsedConstants
        | _ => #[]
      pending := pending ++ dependencies

#check @prepareSealPublication
#check @prepareInformationAnalysisStage
#check @prepareInformationAnalysisExport
