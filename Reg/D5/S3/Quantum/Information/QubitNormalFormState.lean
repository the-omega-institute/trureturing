import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.QubitNormalFormState

noncomputable section
namespace Reg.D5.S3.Quantum.Information.QubitNormalFormState
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.QubitNormalFormState
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1),
    vonNeumannEntropy (qubitState x z h) =
      R.readout () () ((1 + Real.sqrt (x ^ 2 + z ^ 2)) / 2)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 0 1 (by norm_num)
  rw [qubit_state_entropy] at hh
  norm_num [bad, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2⁻¹, 1, ?_⟩
  simp only [actual, realize, Real.binEntropy_one, Real.binEntropy_two_inv]
  exact ne_of_gt (Real.log_pos (by norm_num))
def family : Registration arena (type_of% (@qubit_state_entropy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@qubit_state_entropy, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@qubit_state_entropy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.QubitNormalFormState.unit
  realizationName := `Reg.D5.S3.Quantum.Information.QubitNormalFormState.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.QubitNormalFormState
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Quantum.Information.QubitNormalFormState
