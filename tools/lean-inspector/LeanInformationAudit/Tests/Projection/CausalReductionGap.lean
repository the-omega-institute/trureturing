import LeanInformationAudit.KernelProjection
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

namespace LeanInformationAudit.Tests.Projection.Causal

abbrev catalog : Catalog unifiedArena := Catalog.ofVector
  ![unifiedCounterfactualUnit, unifiedInterventionUnit, unifiedObservationUnit]

/- The landed sum-valued readout deciders contain proposition transports that do not
reduce in the kernel. This is a rejection reproducer, not the required positive causal
projection fixture. No v3 output is written for this unsupported computation. -/
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
  let _ ← liftTermElabM do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels ``catalog)
      (← mkConstWithFreshMVarLevels ``unifiedArena)
      #[``unifiedCounterfactualUnit, ``unifiedInterventionUnit, ``unifiedObservationUnit]
      `Causal ``catalog ``unifiedArena `CausalProjection {
        schedules := #[("obs-int-cf", #[2, 1, 0])] }).run #[]

#print axioms catalog
#print axioms projectionRefinesB_eq_true_iff

end LeanInformationAudit.Tests.Projection.Causal
