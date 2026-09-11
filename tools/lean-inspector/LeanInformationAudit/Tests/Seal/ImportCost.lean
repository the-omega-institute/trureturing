import LeanInformationAudit.SealCommand
open Lean Lean.Elab.Command
run_cmd do
  for name in [`D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog,
      `D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty] do
    if (← getEnv).header.moduleNames.contains name then
      throwError "ImportCost: structural dependency in finite seal closure: {name}"
