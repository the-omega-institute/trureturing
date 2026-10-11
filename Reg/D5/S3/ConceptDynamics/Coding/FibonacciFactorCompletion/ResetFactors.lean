import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
noncomputable section

abbrev weightSignature : Signature where
  Params := List CuLetter
  State _ := List CuLetter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ w v => wordWeight (w ++ v)) (fun e => nomatch e)
def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature
  Law R := (∀ w v, R.readout () w v = wordWeight w + wordWeight v) ∧
    (∀ w, w.length ≤ wordWeight w) ∧ (∀ w, wordWeight w = 0 → w = [])

theorem weight_rejected_law : ¬ weightArena.Law weightRejected := by
  intro h
  have hh := h.1 [] []
  norm_num [weightRejected, realize, wordWeight] at hh

def weightRegistration : Registration weightArena (weightArena.Law weightActual) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨word_weight_geometry, weightRejected, weight_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightRejected, ?_, rfl, weight_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨[], [], [.u], ?_⟩
    simp [weightActual, realize, wordWeight]

def word_weight_geometry_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.word_weight_geometry)
      (type_of% (realize.{0,0,0,0,0} weightSignature
        (fun _ w v => wordWeight (w ++ v)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.word_weight_geometry_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.weightRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} weightSignature
    (fun _ w v => wordWeight (w ++ v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightRegistration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
