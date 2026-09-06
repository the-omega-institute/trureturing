import LeanInformationAudit.KernelProjection
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

namespace LeanInformationAudit.Tests.Projection.CausalGap

abbrev catalog : Catalog unifiedArena := Catalog.ofVector
  ![unifiedCounterfactualUnit, unifiedInterventionUnit, unifiedObservationUnit]

/- The direct route still cannot reduce the frozen sum-valued readout decisions.
The positive CausalProjection fixture exercises the certified reflection bridge. -/
/--
error: reduceEval: failed to evaluate argument
  Decidable.rec (fun h ↦ (fun x ↦ false) h) (fun h ↦ (fun x ↦ true) h)
    (projectionNodeLE (catalog.generatedKernel (insert ⟨1, ⋯⟩ (insert ⟨2, ⋯⟩ Finset.empty)))
      (catalog.generatedKernel (insert ⟨0, ⋯⟩ Finset.empty)))
-/
#guard_msgs in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
run_cmd do
  let _ ← liftTermElabM <| withTransparency .all do
    let original ← mkConstWithFreshMVarLevels ``catalog
    let first ← mkAppM ``Catalog.generatedKernel
      #[original, ← ProjectionProof.selection 3 #[1, 2]]
    let second ← mkAppM ``Catalog.generatedKernel
      #[original, ← ProjectionProof.selection 3 #[0]]
    ProjectionProof.truth (← mkLE first second)

#print axioms catalog
#print axioms projectionRefinesB_eq_true_iff

end LeanInformationAudit.Tests.Projection.CausalGap
