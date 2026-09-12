import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Seal.M3
open Lean Lean.Elab.Command
run_cmd do
  for name in [`D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog,
      `D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty] do
    if (← getEnv).header.moduleNames.contains name then
      throwError "ImportCost: structural dependency in finite seal closure: {name}"
-- M3 imports `SealCommand`, not `Census.Query`; these modules carry no registrations and
-- must stay out of its re-seal trigger set (issue #7266, lane A).
run_cmd do
  for name in [`LeanInformationAudit.Census.Query,
      `D5.S0.Rewriting.Quotients.AnswerabilityCriterion,
      `D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction,
      `D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois,
      `D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw,
      `D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion,
      `D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion,
      `D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty,
      `D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralArena,
      `D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog,
      `D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion,
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
