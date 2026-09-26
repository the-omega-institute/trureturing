import Reg.Support.QubitChordChannels
import Reg.Support.DependentFamily

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open _root_.D5.S3.Quantum.Information.ActualQubitChordObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.QubitChordChannels LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, v, b, hv, _, _, _, _, hvker, _⟩ :=
    (h (1/2) (by norm_num) (by norm_num) processor curve curve_density
      (fun u _ k => processor_exact u k)).1.2
  change v ∈ ((jointObservation processor).comp projectX).kerᗮ at hvker
  rw [erased_observation] at hvker
  exact hv (inner_self_eq_zero.mp
    (Submodule.inner_right_of_mem_orthogonal (by simp) hvker))

theorem variation_proof : Variation arena actual := ⟨actual_two_probe_chord_and_qfi, rejected, rejected_law⟩

theorem sensitivity_proof : Sensitivity arena actual :=
  sole_role_sensitivity arena.Law actual rejected (funext fun e => Empty.elim e) rejected_law

theorem dependence_proof : ObservationalDependence signature actual := by
    intro i
    exact ⟨(), processor, discardProcessor, observations_differ⟩

-- The source assessor reconstructs the original ConstantInfo.type from this
-- complete law and kernel-checks the bridge against that original statement.
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := variation_proof
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem actual_two_probe_chord_and_qfi in arena
  readout via (realize signature (fun _ _ G => jointObservation G) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction
