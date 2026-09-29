import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

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
  let .ok () ← enroll (← getEnv).header.mainModule (← getOptions) name | throwError "setup: ordinary template enrollment failed"
  let env ← getEnv
  let .ok plan := selectedPlan env name | throwError "setup: checked plan absent"
  -- A report must reassess the original body. A public signature-only
  -- environment cannot borrow a plan from a different checked environment.
  let empty ← finalizeImport default #[] {} 0 false false (isModule := true)
  let publicBranch ← (empty.setMainModule env.header.mainModule).addConstAsync name .defn (some .axiom)
  publicBranch.commitConst checked (exportedInfo? := some (.axiomInfo {
    name, levelParams := original.levelParams, type := original.type, isUnsafe := false }))
  publicBranch.commitCheckEnv checked
  let visible := publicBranch.mainEnv.setExporting true
  let some publicInfo := visible.find? name | throwError "setup: public declaration absent"
  unless publicInfo.value?.isNone do throwError "setup: public implementation was exposed"
  setEnv visible
  let hiddenResult ← enroll visible.header.mainModule (← getOptions) name
  let rejected := hiddenResult.isError
  setEnv (resetTemplatePlans env)
  let full ← enroll env.header.mainModule (← getOptions) name

  set saved
  (if rejected then logInfo else logError) m!"[{if rejected then "PASS" else "FAIL"}] report_rejects_missing_original_body"
  (if full.isOk then logInfo else logError) m!"[{if full.isOk then "PASS" else "FAIL"}] report_accepts_checked_original_body"

observe_import_body

end LeanInformationAudit.Tests.DeclaredImportBody
