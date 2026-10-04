import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ G => jointObservation G) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "ActualQubitChordObstruction") "actual_two_probe_chord_and_qfi") "Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction/D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ G => jointObservation G) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction
