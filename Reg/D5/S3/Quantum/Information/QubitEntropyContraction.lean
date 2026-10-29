import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.QubitEntropyContraction
noncomputable section
namespace Reg.D5.S3.Quantum.Information.QubitEntropyContraction
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.QubitEntropyContraction
open _root_.D5.S3.Quantum.Information.QubitNormalFormState
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def readout : Realization signature := realize signature (fun _ _ p q => p ≤ q) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature readout := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [readout, realize] at he

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x z t : ℝ} (hdisk : x ^ 2 + z ^ 2 ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    let hscaled : x ^ 2 + (t * z) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - t ^ 2 by nlinarith [ht.1, ht.2]) (sq_nonneg z)]
    0 ≤ qubitHolevo x (t * z) hscaled ∧
      R.readout () () (qubitHolevo x (t * z) hscaled) (t ^ 2 * qubitHolevo x z hdisk)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact (@h 0 0 0 (by norm_num) (by norm_num)).2
def family : Registration arena (type_of% (@qubit_holevo_contraction)) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨@qubit_holevo_contraction, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law readout bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@qubit_holevo_contraction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.QubitEntropyContraction.unit
  realizationName := `Reg.D5.S3.Quantum.Information.QubitEntropyContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p q => p ≤ q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.QubitEntropyContraction
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Reg.D5.S3.Quantum.Information.QubitEntropyContraction
