import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

namespace LeanInformationAudit.Tests.DeclaredImportBody
open Lean Meta Elab Command TemplateAudit

elab "observe_import_body" : command => do
  let saved ← get
  let name := (← getEnv).header.mainModule.str "publicTemplate"
  let .defnInfo original ← getConstInfo `DTRIndex.A.selected
    | throwError "setup: original definition absent"
  -- Use the compiler's native async declaration API to retain a kernel-checked
  -- private definition and its public signature-only view. No kernel axiom is
  -- added. The legacy inspector cannot itself be imported from a `module` file.
  let branch ← (← getEnv).addConstAsync name .defn (some .axiom)
  setEnv branch.asyncEnv
  liftTermElabM <| addDecl <| .defnDecl {
    name, levelParams := original.levelParams, type := original.type,
    value := original.value, hints := original.hints, safety := original.safety }
  let checked ← getEnv
  branch.commitConst checked (exportedInfo? := some (.axiomInfo {
    name, levelParams := original.levelParams, type := original.type, isUnsafe := false }))
  branch.commitCheckEnv checked
  setEnv branch.mainEnv
  let .ok () ← enroll name | throwError "setup: ordinary template enrollment failed"
  let env ← getEnv
  let .ok plan := selectedPlan env name | throwError "setup: checked plan absent"
  let .ok bytes := planEncoding plan | throwError "setup: checked plan encoding failed"
  let frame : TemplatePlanFrame := {
    key := name.toString.toUTF8, payload := bytes, identity := Sha256.hex bytes }
  -- Build an empty module environment through the compiler's public constructor.
  -- Transport the already kernel-checked declaration through native async views;
  -- this isolates addFrame without reimporting the full test dependency graph.
  let empty ← finalizeImport default #[] {} 0 false false (isModule := true)
  let publicBranch ← (empty.setMainModule env.header.mainModule).addConstAsync name .defn (some .axiom)
  publicBranch.commitConst checked (exportedInfo? := some (.axiomInfo {
    name, levelParams := original.levelParams, type := original.type, isUnsafe := false }))
  publicBranch.commitCheckEnv checked
  let visible := publicBranch.mainEnv.setExporting true
  let some publicInfo := visible.find? name | throwError "setup: public declaration absent"
  unless publicInfo.value?.isNone do throwError "setup: public implementation was exposed"
  let imported := ({} : TemplateIndex).addFrame frame visible plan.enrollmentOwner
  let ok := (imported.lookup name (pure () : Id Unit)).isOk
  let ordinary := ({} : TemplateIndex).addFrame frame env plan.enrollmentOwner
  let full := (ordinary.lookup name (pure () : Id Unit)).isOk
  set saved
  logInfo m!"[{if ok then "PASS" else "FAIL"}] import_never_reaudits_body"
  logInfo m!"[{if full then "PASS" else "FAIL"}] selective_import_within_cap_accepted"

observe_import_body

end LeanInformationAudit.Tests.DeclaredImportBody
