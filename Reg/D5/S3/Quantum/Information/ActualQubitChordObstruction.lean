import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.QubitChordChannels
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Information.ActualQubitChordObstruction.actual_two_probe_chord_and_qfi) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ G => jointObservation G) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "ActualQubitChordObstruction") "actual_two_probe_chord_and_qfi") "Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction/D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ G => jointObservation G) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


namespace DetBloch

/-- Observe the Bloch matrix whose determinant is specified. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => EuclideanSpace ℝ (Fin 3)) (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ r => blochMatrix 1 r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : EuclideanSpace ℝ (Fin 3),
    (R.readout () () r).det = (((1 - ‖r‖ ^ 2) / 4 : ℝ) : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, EuclideanSpace.single 2 1, ?_⟩
  change blochMatrix 1 0 ≠ blochMatrix 1 (EuclideanSpace.single 2 1)
  intro he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) he
  norm_num [blochMatrix, PiLp.single_apply] at hc

def source_registration : Registration arena (type_of% @det_bloch) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨det_bloch, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@det_bloch) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.DetBloch.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.DetBloch.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => blochMatrix 1 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end DetBloch

namespace Pure

/-- Observe the matrix on the right of the pure-state idempotence identity. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => EuclideanSpace ℝ (Fin 3)) (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ r => blochMatrix 1 r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ = 1 →
    blochMatrix 1 r * blochMatrix 1 r = R.readout () () r

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : ‖(EuclideanSpace.single 2 1 : EuclideanSpace ℝ (Fin 3))‖ = 1 := by simp
  have he := h _ hr
  change blochMatrix 1 (EuclideanSpace.single 2 1) *
    blochMatrix 1 (EuclideanSpace.single 2 1) = 0 at he
  rw [pure _ hr] at he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) he
  norm_num [blochMatrix, PiLp.single_apply] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, EuclideanSpace.single 2 1, ?_⟩
  change blochMatrix 1 0 ≠ blochMatrix 1 (EuclideanSpace.single 2 1)
  intro he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) he
  norm_num [blochMatrix, PiLp.single_apply] at hc

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Information.ActualQubitChordObstruction.pure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pure, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.ActualQubitChordObstruction.pure)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.Pure.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction.Pure.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => blochMatrix 1 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualQubitChordObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Pure

end Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction
