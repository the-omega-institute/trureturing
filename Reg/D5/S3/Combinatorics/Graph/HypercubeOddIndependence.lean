import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeOddIndependence
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.HypercubeOddIndependence
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.HypercubeOddIndependence

abbrev errorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def errorActual : Realization errorSignature :=
  realize errorSignature (fun _ _ x => |x|) (fun e => nomatch e)

def errorRejected : Realization errorSignature :=
  realize errorSignature (fun _ _ _ => 1) (fun e => nomatch e)

def errorArena : Arena where
  signature := errorSignature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ d : ℕ,
    Even d → D ≤ d →
      R.readout () () ((oddIndependenceNumber d : ℝ) / (2 ^ d : ℝ) - 1 / 2) < ε

private theorem error_rejected_law : ¬ errorArena.Law errorRejected := by
  intro h
  obtain ⟨D, hD⟩ := h (1/2) (by norm_num)
  have hh := hD (2 * D) (by exact ⟨D, by omega⟩) (by omega)
  change (1 : ℝ) < 1 / 2 at hh
  norm_num at hh

def errorRecord : Registration errorArena (type_of% (@result)) where
  actual := errorActual
  bridge := Iff.rfl
  variation := ⟨result, errorRejected, error_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    errorArena.Law errorActual errorRejected error_rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change |(0 : ℝ)| ≠ |(1 : ℝ)|
    norm_num

noncomputable def result_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.HypercubeOddIndependence.result)
    (type_of% (realize errorSignature (fun _ _ x => |x|) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.HypercubeOddIndependence.error_information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeOddIndependence.errorRecord
  realizationSource := none
  generated := false
  arena := .source ⟨errorArena⟩
  objectArena := .source ⟨errorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source errorArena ⟨errorRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize errorSignature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeOddIndependence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms errorRecord
#print axioms result_registration

end Reg.D5.S3.Combinatorics.Graph.HypercubeOddIndependence
