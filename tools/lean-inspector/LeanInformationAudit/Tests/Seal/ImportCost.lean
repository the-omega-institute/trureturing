import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Seal.M3
open Lean Lean.Elab.Command
run_cmd do
  -- Walk the import metadata already present in this environment. Loading a
  -- second environment would duplicate the entire finite seal dependency set.
  let env ← getEnv
  let mut pending := #[`LeanInformationAudit.SealCommand]
  let mut finiteModules : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless finiteModules.contains name do
      finiteModules := finiteModules.insert name
      let some idx := env.getModuleIdx? name
        | throwError "ImportCost: missing reflected module: {name}"
      let some data := env.header.moduleData[idx.toNat]?
        | throwError "ImportCost: missing reflected import metadata: {name}"
      pending := pending ++ data.imports.map (·.module)
  for name in [`D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog,
      `D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty] do
    if finiteModules.contains name then
      throwError "ImportCost: structural dependency in finite seal closure: {name}"
-- M3 needs StructuralCatalog for its zero-capture certificates, but no census modules.
-- Keep the remaining registration-free dependencies out of its trigger set (#7266).
run_cmd do
  for name in [`LeanInformationAudit.Census.Query,
      `LeanInformationAudit.Census.Certificate,
      `LeanInformationAudit.Census.Coverage,
      `LeanInformationAudit.Census.Manifest,
      `LeanInformationAudit.Census.Ownership,
      `LeanInformationAudit.Census.Report,
      `LeanInformationAudit.Census.Stream,
      `LeanInformationAudit.DispositionCensus,
      `LeanInformationAudit.DispositionEvidence,
      `LeanInformationAudit.StructuralRealization,
      `LeanInformationAudit.StructuralRegistrationGates] do
    if (← getEnv).header.moduleNames.contains name then
      throwError "ImportCost: M3 import closure widened: {name}"
run_cmd do
  let inRepo := (← getEnv).header.moduleNames.filter fun name =>
    name != `LeanInformationAudit.Tests.Seal.M3 &&
      LeanInformationAudit.Repository.isModule name
  -- Count the split closure's five Interface owners as well as its 136 D5/Impl modules.
  let interface := inRepo.filter ((`LeanInformationAuditInterface).isPrefixOf ·)
  if inRepo.size > 141 || interface.size != 5 then
    throwError "ImportCost: M3 closure changed: modules={inRepo.size} interface={interface.size}"
  logInfo m!"DTR_M3_IMPORTS modules={inRepo.size} limit=141 interface={interface.size}"
