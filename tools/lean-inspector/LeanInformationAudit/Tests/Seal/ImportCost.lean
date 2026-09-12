import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Seal.M3
open Lean Lean.Elab.Command
run_cmd do
  let finiteEnv ← importModules #[{ module := `LeanInformationAudit.SealCommand }] {}
  for name in [`D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog,
      `D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty] do
    if finiteEnv.header.moduleNames.contains name then
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
      (name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit.")
  if inRepo.size > 125 then
    throwError "ImportCost: M3 import closure exceeded 125 modules: {inRepo.size}"
