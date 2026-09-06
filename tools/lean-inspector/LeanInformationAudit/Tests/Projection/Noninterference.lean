import LeanInformationAudit.Tests.Projection.V3Seal
import LeanInformationAudit.Projection.OutputOnlyAudit

open Lean Lean.Elab.Command LeanInformationAudit

private def fileReadAfterSeal (producer : CommandElab) : CommandElab := fun stx => do
  producer stx
  let contents ← liftIO <| IO.FS.readFile "analysis.json"
  if contents.contains "nodes" then setEnv (← getEnv)

private def processReadAfterSeal (producer : CommandElab) : CommandElab := fun stx => do
  producer stx
  let result ← liftIO <| IO.Process.output { cmd := "/bin/cat", args := #["analysis.json"] }
  if result.stdout.contains "nodes" then setEnv (← getEnv)

private def publicationAfterSeal (producer : CommandElab) : CommandElab := fun stx => do
  producer stx
  setEnv (← getEnv)

/--
info: IE-C043 KernelProjectionUsedForAdmission consumer=DirectFileMutation field=publication-order root=LeanInformationAudit.Tests.Projection.Noninterference catalog=system
IE-C043 KernelProjectionUsedForAdmission consumer=SubprocessMutation field=publication-order root=LeanInformationAudit.Tests.Projection.Noninterference catalog=system
IE-C043 KernelProjectionUsedForAdmission consumer=PublicationOrderMutation field=publication-order root=LeanInformationAudit.Tests.Projection.Noninterference catalog=system
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let some entry := env.constants.toList.find? fun (name, _) =>
      (privateToUserName name).toString == "LeanInformationAudit.elabSealInformationTheory"
    | throwError "missing real seal elaborator"
  let mut messages := #[]
  for (wrapper, name) in #[( ``fileReadAfterSeal, `DirectFileMutation),
      (``processReadAfterSeal, `SubprocessMutation),
      (``publicationAfterSeal, `PublicationOrderMutation)] do
    let value := mkApp (mkConst wrapper) (mkConst entry.1)
    liftCoreM <| addDecl (.defnDecl {
      name, levelParams := [], type := entry.2.type, value, hints := .abbrev, safety := .safe })
    match auditSealOutputOnly (← getEnv) name env.header.mainModule with
    | .error message => messages := messages.push message
    | .ok () => messages := messages.push s!"ACCEPTED {name}"
  logInfo (String.intercalate "\n" messages.toList)

/-- info: seal publication has no artifact input -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let some entry := env.constants.toList.find? fun (name, _) =>
      (privateToUserName name).toString == "LeanInformationAudit.elabSealInformationTheory"
    | throwError "missing real seal elaborator"
  match auditSealOutputOnly env entry.1 env.header.mainModule with
  | .ok () => pure ()
  | .error message => throwError message
  unless env.contains `LeanInformationAudit.Tests.Projection.V3Seal.__system_catalog_irredundant do
    throwError "seal publication missing"
  logInfo "seal publication has no artifact input"
