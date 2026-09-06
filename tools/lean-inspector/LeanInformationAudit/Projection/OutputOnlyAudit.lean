import Lean

namespace LeanInformationAudit
open Lean Lean.Elab.Command

/-!
T-041 is closed by destination-free publication and terminal export commands.

`#seal_information_theory` has no output clause. Its fixed terminal combinator
discards the command syntax and invokes a `CommandElabM Unit` publication closure.
The owned-definition audit rejects ambient command-reference access, direct
runtime input capabilities, and the enumerated Lean-core module loaders before
that closure runs. The seal may publish declarations and may log, but it cannot
write an artifact.

`#stage_information_analysis root <id>` receives only a root name and applies the
same owned-definition audit before publishing analysis for an already-sealed root.
Its syntax has no artifact selector or destination.

`#export_information_analysis` owns all destination syntax. Its preparation
closure receives only a root and artifact kinds. The fixed terminal combinator
finishes preparation before entering an `IO`-only writer, and the export closure
audit rejects environment mutation, declaration staging, command elaboration,
runtime inputs, and module loaders. The writer is audited with `writeFile` as its
only runtime capability.

Residual: definitions owned by Lean/Init/Std/Mathlib remain opaque boundary
nodes. The explicit lists close the known current-reference and module-loader
channels at that boundary, but this is not an OS sandbox or a claim that every
future Lean-core capability is classified. Owned unsafe, extern, implemented_by,
and compiler-generated partial bodies are rejected fail-closed.
-/

inductive ArtifactKind where
  | seal | analysis | ascii
  deriving BEq, Inhabited, Repr

structure AnalysisExportPlan where
  artifacts : List (ArtifactKind × String)

syntax (name := sealInformationTheoryCmd) "#seal_information_theory" : command

syntax (name := stageInformationAnalysisCmd)
  "#stage_information_analysis" ident ident : command

syntax (name := exportInformationAnalysisCmd)
  "#export_information_analysis" ident ident (" output " str)?
    (" analysis_output " str)? (" ascii_output " str)? : command

/-- Seal syntax is deliberately discarded before publication. -/
def terminalSealCommand (publication : CommandElabM Unit) : CommandElab :=
  fun _ => publication

private def absoluteName (name : Name) : Name :=
  if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else name

private def commandRoot (stx : Syntax) : Name :=
  absoluteName stx[2].getId

/-- Staging receives only the root name, with no artifact or destination syntax. -/
def terminalInformationAnalysisStageCommand
    (publication : Name → CommandElabM Unit) : CommandElab :=
  fun stx => publication (commandRoot stx)

/-- Inspect clause presence only; do not inspect any destination literal. -/
private def requestedExportArtifacts (stx : Syntax) : List ArtifactKind :=
  [(.seal, stx[3]), (.analysis, stx[4]), (.ascii, stx[5])].filterMap fun (kind, clause) =>
    if clause.getNumArgs == 0 then none else some kind

/-- The terminal writer has no command state or environment capability. -/
private def writeAnalysisArtifacts (stx : Syntax) (plan : AnalysisExportPlan) : IO Unit := do
  let `( #export_information_analysis $_rootMarker:ident $_rootId:ident $[output $outputPath:str]?
      $[analysis_output $analysisPath:str]? $[ascii_output $asciiPath:str]? ) := stx
    | return
  for (kind, contents) in plan.artifacts do
    let destination := match kind with
      | .seal => outputPath
      | .analysis => analysisPath
      | .ascii => asciiPath
    if let some destination := destination then
      IO.FS.writeFile destination.getString contents

/-- Preparation finishes before the command enters the IO-only writer. -/
def terminalInformationAnalysisExportCommand
    (preparation : Name → List ArtifactKind → CommandElabM AnalysisExportPlan) :
    CommandElab := fun stx => do
  let plan ← preparation (commandRoot stx) (requestedExportArtifacts stx)
  liftIO <| writeAnalysisArtifacts stx plan

/-- Exact seal runtime allowlist, pinned by Noninterference.Contract. -/
def sealIOAllowlist : List Name := [``Lean.logInfo]

/-- Current-reference capabilities can recover the ambient seal command syntax. -/
def sealSyntaxDenylist : List Name :=
  [``Lean.Elab.Command.getRef, ``MonadRef.getRef, ``withRef, ``MonadRef.withRef]

/-- Supported Lean-core loaders that bypass the IO/FS namespace predicate. -/
def leanCoreFileLoaderDenylist : List Name :=
  [``Lean.findOLean, ``Lean.readModuleData, ``Lean.readModuleDataParts,
    ``Lean.ModuleSetup.load]

/-- Export may read the sealed environment but cannot change or elaborate it. -/
def exportEnvironmentMutationDenylist : List Name :=
  [``Lean.setEnv, ``MonadEnv.modifyEnv, ``Lean.withEnv,
    ``Lean.withoutModifyingEnv, ``Lean.withoutModifyingEnv',
    ``Lean.addDecl, ``Lean.addAndCompile, ``Lean.Environment.addDeclCore,
    ``Lean.Elab.Command.elabCommand, ``Lean.Elab.Command.elabCommandTopLevel,
    ``Lean.Elab.Command.liftCoreM]

private def ownedByInspector (env : Environment) (name : Name) : Bool :=
  let owner := (env.getModuleIdxFor? name).map fun index =>
    env.allImportedModuleNames[index.toNat]!
  (`LeanInformationAudit).isPrefixOf (owner.getD env.header.mainModule)

private def scannedRuntimeCapability (env : Environment) (name : Name) : Bool :=
  let scanned := [(`IO), (`System), (`Lean.FS)].any (·.isPrefixOf name) ||
    name == ``Lean.logInfo
  let dataOnly := (env.find? name).any fun info =>
    info.type.getForallBody.isSort || match info with
      | .ctorInfo _ | .inductInfo _ => true
      | _ => false
  scanned && !dataOnly

private def diagnostic (consumer : Name) (field : String) (rootId : Name) : String :=
  s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName consumer} \
field={field} root={rootId} catalog=system"

private structure AuditPolicy where
  runtimeAllowlist : List Name := []
  directDenylist : List Name := []

private def declarationDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .defnInfo info => info.value.getUsedConstants
  | .opaqueInfo info => info.value.getUsedConstants
  | _ => #[]

private def auditOwnedClosure (env : Environment) (entry rootId : Name)
    (policy : AuditPolicy) : Except String Unit := do
  let mut pending := #[entry]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    unless ownedByInspector env name do continue
    if let some info := env.find? name then
      let opaquePartial := match info with
        | .opaqueInfo _ => (env.find? (Compiler.mkUnsafeRecName name)).any (·.isPartial)
        | _ => false
      if info.isUnsafe || info.isPartial || (Compiler.getImplementedBy? env name).isSome ||
          (getExternAttrData? env name).isSome || opaquePartial then
        throw (diagnostic name s!"capability:{privateToUserName name}" rootId)
      for dependency in (declarationDependencies info).qsort Name.lt do
        if policy.directDenylist.contains dependency ||
            leanCoreFileLoaderDenylist.contains dependency then
          throw (diagnostic name s!"capability:{dependency}" rootId)
        if scannedRuntimeCapability env dependency &&
            !policy.runtimeAllowlist.contains dependency then
          throw (diagnostic name s!"capability:{dependency}" rootId)
        pending := pending.push dependency

private def sealTerminalShape (value : Expr) : Bool := Id.run do
  let .lam _ _ terminal _ := value.consumeMData | return false
  let .lam _ _ body _ := terminal.consumeMData | return false
  return body.consumeMData == .bvar 1

private def exportTerminalShape (value : Expr) : Bool := Id.run do
  let .lam _ _ (.lam _ _ body _) _ := value.consumeMData | return false
  unless body.isAppOfArity ``Bind.bind 6 do return false
  let commandMonad := mkConst ``Lean.Elab.Command.CommandElabM
  let commandBind := mkApp2 (mkConst ``Monad.toBind [0, 0]) commandMonad
    (mkConst ``Lean.Elab.Command.instMonadCommandElabM)
  unless body.getArg! 0 == commandMonad && body.getArg! 1 == commandBind do return false
  let preparation := mkApp2 (.bvar 1)
    (mkApp (mkConst ``commandRoot) (.bvar 0))
    (mkApp (mkConst ``requestedExportArtifacts) (.bvar 0))
  unless body.getArg! 4 == preparation do return false
  let .lam _ _ tail _ := body.getArg! 5 | return false
  unless tail.isAppOfArity ``Lean.Elab.Command.liftIO 2 do return false
  return tail.appArg! == mkApp2 (mkConst ``writeAnalysisArtifacts) (.bvar 1) (.bvar 0)

private def sealPublicationType : Expr :=
  mkApp (mkConst ``Lean.Elab.Command.CommandElabM) (mkConst ``Unit)

private def stagePublicationType : Expr :=
  Expr.forallE `_rootId (mkConst ``Name) sealPublicationType .default

private def stageTerminalShape (value : Expr) : Bool := Id.run do
  let .lam _ _ (.lam _ _ body _) _ := value.consumeMData | return false
  return body.consumeMData == mkApp (.bvar 1) (mkApp (mkConst ``commandRoot) (.bvar 0))

private def exportPreparationType : Expr :=
  Expr.forallE `_rootId (mkConst ``Name)
    (Expr.forallE `requested (mkApp (mkConst ``List [0]) (mkConst ``ArtifactKind))
      (mkApp (mkConst ``Lean.Elab.Command.CommandElabM)
        (mkConst ``AnalysisExportPlan)) .default) .default

/-- Verify the path-free seal combinator and audit its publication closure. -/
def auditSealOutputOnly (env : Environment) (entry rootId : Name) : Except String Unit := do
  let failure := diagnostic entry "publication-order" rootId
  let some (.defnInfo commandInfo) := env.find? entry | throw failure
  let some (.defnInfo terminalInfo) := env.find? ``terminalSealCommand | throw failure
  unless sealTerminalShape terminalInfo.value do throw failure
  let commandValue := commandInfo.value.consumeMData
  unless commandValue.isAppOfArity ``terminalSealCommand 1 do throw failure
  let some publication := commandValue.appArg!.constName? | throw failure
  unless (env.find? publication).any (·.type == sealPublicationType) do
    throw (diagnostic publication "publication-signature" rootId)
  auditOwnedClosure env publication rootId {
    runtimeAllowlist := sealIOAllowlist
    directDenylist := sealSyntaxDenylist
  }

/-- Verify destination-free staging and audit its publication closure like seal. -/
def auditInformationAnalysisStage (env : Environment) (entry rootId : Name) :
    Except String Unit := do
  let failure := diagnostic entry "staging-order" rootId
  let some (.defnInfo commandInfo) := env.find? entry | throw failure
  let some (.defnInfo terminalInfo) :=
      env.find? ``terminalInformationAnalysisStageCommand | throw failure
  unless stageTerminalShape terminalInfo.value do throw failure
  let commandValue := commandInfo.value.consumeMData
  unless commandValue.isAppOfArity ``terminalInformationAnalysisStageCommand 1 do
    throw failure
  let some publication := commandValue.appArg!.constName? | throw failure
  unless (env.find? publication).any (·.type == stagePublicationType) do
    throw (diagnostic publication "staging-signature" rootId)
  auditOwnedClosure env publication rootId {
    runtimeAllowlist := sealIOAllowlist
    directDenylist := sealSyntaxDenylist
  }

/-- Verify terminal export ordering and audit preparation plus the IO-only writer. -/
def auditInformationAnalysisExport (env : Environment) (entry rootId : Name) :
    Except String Unit := do
  let failure := diagnostic entry "export-order" rootId
  let some (.defnInfo commandInfo) := env.find? entry | throw failure
  let some (.defnInfo terminalInfo) :=
      env.find? ``terminalInformationAnalysisExportCommand | throw failure
  unless exportTerminalShape terminalInfo.value do throw failure
  let commandValue := commandInfo.value.consumeMData
  unless commandValue.isAppOfArity ``terminalInformationAnalysisExportCommand 1 do
    throw failure
  let some preparation := commandValue.appArg!.constName? | throw failure
  unless (env.find? preparation).any (·.type == exportPreparationType) do
    throw (diagnostic preparation "export-signature" rootId)
  let directDenylist := sealSyntaxDenylist ++ exportEnvironmentMutationDenylist
  auditOwnedClosure env preparation rootId { directDenylist }
  auditOwnedClosure env ``writeAnalysisArtifacts rootId {
    runtimeAllowlist := [``IO.FS.writeFile]
    directDenylist
  }

end LeanInformationAudit
