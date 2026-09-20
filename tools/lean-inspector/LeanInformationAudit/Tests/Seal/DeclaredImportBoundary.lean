import LeanInformationAudit.SealCommand

open Lean Elab Command

-- This observer imports only the finite seal path. M3, FrozenRoots and
-- ImportCost are checked by the separate static source-closure walk.
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter LeanInformationAudit.Repository.isModule
  let core := #[`LeanInformationAudit.Registry, `LeanInformationAudit.Syntax,
    `LeanInformationAudit.SealCommand, `LeanInformationAudit.Registry.Repository].all modules.contains
  (if core then logInfo else logError) m!"[{if core then "PASS" else "FAIL"}] existing_finite_seal_core_accepted"
  -- The split closure has 98 D5/Impl modules and five Interface source owners.
  let interface := modules.filter ((`LeanInformationAuditInterface).isPrefixOf ·)
  let unchanged := modules.size == 103 && interface.size == 5
  (if unchanged then logInfo else logError) m!"[{if unchanged then "PASS" else "FAIL"}] finite_seal_family_closure_unchanged"
  logInfo m!"DTR_FINITE_IMPORTS modules={modules.size} expected=103 interface={interface.size}"
