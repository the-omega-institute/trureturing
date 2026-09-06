import Lean

namespace LeanInformationAudit
open Lean Lean.Elab.Command

/-!
T-041 boundary: publication receives only artifact kinds, never output syntax or
destination strings. Only the terminal IO writer extracts destination literals.
The audit follows elaborated definition/opaque bodies owned by modules under
LeanInformationAudit (including private helpers), stopping at other modules.
Direct runtime constants under IO, System and Lean.FS are default-denied except
sealIOAllowlist. Type-valued constants (for example IO.Error and IO.RealWorld)
are not runtime capabilities; their types end in Sort. No runtime lifting
instance is exempted. Reachable own unsafe, extern and implemented_by constants
are rejected, as are partial functions with compiler-supplied bodies.

Residual: Lean/Init/Std/Mathlib bodies are opaque boundary nodes. Lean-core
file readers outside the listed namespaces (for example module-data loaders),
dynamic evaluation, initialization and callbacks behind those boundaries are
out of scope. This is not an OS sandbox or a claim of full-core purity. Attempt
6's clock/evalExpr/addAndCompile transitive-closure counterexamples still stand.
-/

inductive ArtifactKind where
  | v2 | analysis | ascii
  deriving BEq, Inhabited, Repr

structure SealPublicationPlan where
  staged : Environment
  artifacts : List (ArtifactKind × String)

syntax (name := sealInformationTheoryCmd)
  "#seal_information_theory" (" output " str)?
    (" analysis_output " str)? (" ascii_output " str)? : command

/-- Inspect clause presence only; do not inspect any string-literal leaf. -/
private def requestedSealArtifacts (stx : Syntax) : List ArtifactKind :=
  [(.v2, stx[1]), (.analysis, stx[2]), (.ascii, stx[3])].filterMap fun (kind, clause) =>
    if clause.getNumArgs == 0 then none else some kind

/-- The terminal writer has no command state or environment capability. -/
private def writeSealArtifacts (stx : Syntax) (plan : SealPublicationPlan) : IO Unit := do
  let `( #seal_information_theory $[output $outputPath:str]?
      $[analysis_output $analysisPath:str]? $[ascii_output $asciiPath:str]? ) := stx
    | throw <| IO.userError "unsupported seal output syntax"
  for (kind, contents) in plan.artifacts do
    let destination := match kind with
      | .v2 => outputPath
      | .analysis => analysisPath
      | .ascii => asciiPath
    if let some destination := destination then
      IO.FS.writeFile destination.getString contents

/-- Publication must finish before entering IO, and IO has no command continuation.
In particular, writer failure cannot invoke a rollback of the published environment. -/
def terminalSealCommand (publication : List ArtifactKind → CommandElabM SealPublicationPlan) :
    CommandElab := fun stx => do
  let plan ← publication (requestedSealArtifacts stx)
  liftIO <| writeSealArtifacts stx plan

private def terminalShape (value : Expr) : Bool := Id.run do
  let .lam _ _ (.lam _ _ body _) _ := value.consumeMData | return false
  unless body.isAppOfArity ``Bind.bind 6 do return false
  let commandMonad := mkConst ``Lean.Elab.Command.CommandElabM
  let commandBind := mkApp2 (mkConst ``Monad.toBind [0, 0]) commandMonad
    (mkConst ``Lean.Elab.Command.instMonadCommandElabM)
  unless body.getArg! 0 == commandMonad && body.getArg! 1 == commandBind do return false
  unless body.getArg! 4 == mkApp (.bvar 1)
      (mkApp (mkConst ``requestedSealArtifacts) (.bvar 0)) do return false
  let .lam _ _ tail _ := body.getArg! 5 | return false
  unless tail.isAppOfArity ``Lean.Elab.Command.liftIO 2 do return false
  return tail.appArg! == mkApp2 (mkConst ``writeSealArtifacts) (.bvar 1) (.bvar 0)

/-- Exact runtime-capability allowlist, pinned by Noninterference.Contract. -/
def sealIOAllowlist : List Name := [``IO.FS.writeFile, ``Lean.logInfo]

private def ownedByInspector (env : Environment) (name : Name) : Bool :=
  let owner := (env.getModuleIdxFor? name).map fun index =>
    env.allImportedModuleNames[index.toNat]!
  (`LeanInformationAudit).isPrefixOf (owner.getD env.header.mainModule)

private def scannedCapability (env : Environment) (name : Name) : Bool :=
  let scanned := [(`IO), (`System), (`Lean.FS)].any (·.isPrefixOf name) ||
    name == ``Lean.logInfo
  scanned && !(env.find? name).any (·.type.getForallBody.isSort)

/-- Audit before invoking publication. Writing is allowlisted only in the terminal
phase; even an allowlisted write inside the publication closure fails ordering. -/
def auditSealOutputOnly (env : Environment) (entry root : Name) : Except String Unit := do
  let failure := s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName entry} \
field=publication-order root={root} catalog=system"
  let some (.defnInfo commandInfo) := env.find? entry | throw failure
  let some (.defnInfo terminalInfo) := env.find? ``terminalSealCommand | throw failure
  unless terminalShape terminalInfo.value do throw failure
  let commandValue := commandInfo.value.consumeMData
  unless commandValue.isAppOfArity ``terminalSealCommand 1 do throw failure
  let some publication := commandValue.appArg!.constName? | throw failure
  let publicationType := Expr.forallE `requested
    (mkApp (mkConst ``List [0]) (mkConst ``ArtifactKind))
    (mkApp (mkConst ``CommandElabM) (mkConst ``SealPublicationPlan)) .default
  unless (env.find? publication).any (·.type == publicationType) do
    throw s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName publication} field=publication-signature"
  let mut pending := #[publication]
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
        throw s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName name} capability={privateToUserName name}"
      let dependencies := match info with
        | .defnInfo info => info.value.getUsedConstants
        | .opaqueInfo info => info.value.getUsedConstants
        | _ => #[]
      for dependency in dependencies.qsort Name.lt do
        if #[``IO.FS.writeFile, ``IO.FS.createDirAll, ``writeSealArtifacts,
            ``terminalSealCommand].contains dependency then throw failure
        if scannedCapability env dependency && !sealIOAllowlist.contains dependency then
          throw s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName name} capability={dependency}"
        pending := pending.push dependency

end LeanInformationAudit
