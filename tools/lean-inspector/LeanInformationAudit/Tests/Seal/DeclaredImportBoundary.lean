import LeanInformationAudit.SealCommand

open Lean Elab Command

-- This observer imports only the finite seal path. M3, FrozenRoots and
-- ImportCost are checked by the separate static source-closure walk.
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun name =>
    name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit."
  let core := #[`LeanInformationAudit.Registry, `LeanInformationAudit.Syntax,
    `LeanInformationAudit.SealCommand, `LeanInformationAudit.Registry.Repository].all modules.contains
  (if core then logInfo else logError) m!"[{if core then "PASS" else "FAIL"}] existing_finite_seal_core_accepted"
  -- Rooted source IO adds Registry.Repository to the existing 98-module closure.
  (if modules.size == 99 then logInfo else logError) m!"[{if modules.size == 99 then "PASS" else "FAIL"}] finite_seal_family_closure_unchanged"
  logInfo m!"DTR_FINITE_IMPORTS modules={modules.size} expected=99"
