import LeanInformationAudit.SealCommand

open Lean Elab Command

-- This observer imports only the finite seal path. M3, FrozenRoots and
-- ImportCost are checked by the separate static source-closure walk.
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter LeanInformationAudit.Repository.isModule
  logInfo m!"DTR_FINITE_MODULE_SET {(toJson (modules.map Name.toString |>.qsort (· < ·))).compress}"
  let core := #[`LeanInformationAudit.Registry, `LeanInformationAudit.Syntax,
    `LeanInformationAudit.SealCommand, `LeanInformationAudit.Registry.Repository,
    `LeanInformationAudit.Registry.ArenaProvenance].all modules.contains
  (if core then logInfo else logError) m!"[{if core then "PASS" else "FAIL"}] existing_finite_seal_core_accepted"
  for name in #[`LeanInformationAudit.FiniteLawVariation,
      `LeanInformationAudit.FiniteSlotSensitivity] do
    unless (env.getModuleIdxFor? name).map (env.header.moduleNames[·]!) ==
        some `D5.S3.ConceptDynamics.RegistrationWitnesses do
      throwError "finite seal mathematical provider owner changed: {name}"
  unless (env.getModuleIdxFor? `LeanInformationAudit.InformationSourceSnapshot).map
      (env.header.moduleNames[·]!) == some `LeanInformationAuditInterface.RootContract do
    throwError "finite seal snapshot record owner changed"
  for removed in #[`LeanInformationAudit.RootContract, `LeanInformationAudit.SnapshotTypes,
      `LeanInformationAudit.RegistrationWitnesses] do
    if modules.contains removed then throwError "retired owner returned: {removed}"
  -- The split closure has 97 D5/Impl modules and five Interface source owners.
  let interface := modules.filter ((`LeanInformationAuditInterface).isPrefixOf ·)
  let unchanged := modules.size == 102 && interface.size == 5
  (if unchanged then logInfo else logError) m!"[{if unchanged then "PASS" else "FAIL"}] finite_seal_family_closure_unchanged"
  logInfo m!"DTR_FINITE_IMPORTS modules={modules.size} expected=102 interface={interface.size}"
