import Reg.Support.CausalSourceFamily

namespace Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open Reg.Support.CausalSourceFamily
open LeanInformationAudit

/-- An additional source-family occurrence preserves the complete original statement. -/
noncomputable def registration : Registration strictnessArena (Strictness actual) where
  actual := actual
  bridge := Iff.rfl
  variation := strictness_variation
  sensitivity := strictness_sensitivity
  dependence := dependence

register_information_theorem counterfactual_kernel_strictly_finer in strictnessArena
  readout via (realize signature actual.readout actual.anchor)
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "body", "body", "domain", "fn", "arg"], stateBinder := 0 },
      { path := #["fn", "arg", "body", "body", "body", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily
