import LeanInformationAudit.SealCommand

open Lean Elab Command

-- This observer imports only the finite seal path. M3, FrozenRoots and
-- ImportCost are checked by the separate static source-closure walk.
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun name =>
    name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit."
  let core := #[`LeanInformationAudit.Registry, `LeanInformationAudit.Syntax,
    `LeanInformationAudit.SealCommand].all modules.contains
  logInfo m!"[{if core then "PASS" else "FAIL"}] existing_finite_seal_core_accepted"
  logInfo m!"[{if modules.size == 89 then "PASS" else "FAIL"}] finite_seal_family_closure_unchanged"
  logInfo m!"DTR_FINITE_IMPORTS modules={modules.size} expected=89"
