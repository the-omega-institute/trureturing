import Lean

namespace LeanInformationAudit
open Lean Lean.Elab.Command

/-- The terminal writer has no command state or environment capability. -/
private def writeSealArtifacts (artifacts : Array (String × String)) : IO Unit :=
  artifacts.forM fun (path, contents) => IO.FS.writeFile path contents

/-- Publication must finish before entering IO, and IO has no command continuation.
In particular, writer failure cannot invoke a rollback of the published environment. -/
def terminalSealCommand (publication : Syntax → CommandElabM (Array (String × String))) :
    CommandElab := fun stx => do
  let artifacts ← publication stx
  liftIO <| writeSealArtifacts artifacts

private def terminalShape (value : Expr) : Bool := Id.run do
  let .lam _ _ (.lam _ _ body _) _ := value.consumeMData | return false
  unless body.isAppOfArity ``Bind.bind 6 do return false
  let commandMonad := mkConst ``Lean.Elab.Command.CommandElabM
  let commandBind := mkApp2 (mkConst ``Monad.toBind [0, 0]) commandMonad
    (mkConst ``Lean.Elab.Command.instMonadCommandElabM)
  unless body.getArg! 0 == commandMonad && body.getArg! 1 == commandBind do return false
  unless body.getArg! 4 == mkApp (.bvar 1) (.bvar 0) do return false
  let .lam _ _ tail _ := body.getArg! 5 | return false
  unless tail.isAppOfArity ``Lean.Elab.Command.liftIO 2 do return false
  return tail.appArg! == mkApp (mkConst ``writeSealArtifacts) (.bvar 0)

/-- Check the command's elaborated structure, not a taxonomy of input effects. The sole
command continuation is the terminal IO writer above. Traverse publication helpers only to
check that artifact writing has not been moved into the publication phase. Lean's internal
elaboration dependencies remain trusted; this is an ordering boundary, not an OS sandbox. -/
def auditSealOutputOnly (env : Environment) (entry root : Name) : Except String Unit := do
  let failure := s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName entry} \
field=publication-order root={root} catalog=system"
  let some (.defnInfo commandInfo) := env.find? entry | throw failure
  let some (.defnInfo terminalInfo) := env.find? ``terminalSealCommand | throw failure
  unless terminalShape terminalInfo.value do throw failure
  let commandValue := commandInfo.value.consumeMData
  unless commandValue.isAppOfArity ``terminalSealCommand 1 do throw failure
  let some publication := commandValue.appArg!.constName? | throw failure
  let mut pending := #[publication]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if #[``IO.FS.writeFile, ``writeSealArtifacts, ``terminalSealCommand].contains name then
      throw failure
    let owner := (env.getModuleIdxFor? name).map fun index =>
      env.allImportedModuleNames[index.toNat]!
    if owner.any (fun moduleName => (`Lean).isPrefixOf moduleName ||
        (`Init).isPrefixOf moduleName || (`Std).isPrefixOf moduleName) then
      continue
    if let some info := env.find? name then
      match info with
      | .defnInfo info =>
        pending := pending ++ info.value.getUsedConstants
      | .opaqueInfo info =>
        pending := pending ++ info.value.getUsedConstants
      | _ => pure ()

end LeanInformationAudit
