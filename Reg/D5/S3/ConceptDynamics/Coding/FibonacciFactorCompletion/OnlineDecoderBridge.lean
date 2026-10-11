import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
noncomputable section

abbrev windowSignature : Signature where
  Params := CLabel
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev bitSignature : Signature where
  Params := Unit
  State _ := CLabel
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def windowActual : Realization windowSignature :=
  realize.{0,0,0,0,0} windowSignature (fun _ l i => labelBit l i.val) (fun e => nomatch e)
def windowRejected : Realization windowSignature :=
  realize.{0,0,0,0,0} windowSignature (fun _ _ _ => true) (fun e => nomatch e)

abbrev windowArena : Arena where
  signature := windowSignature
  Law R := ∀ (l : CLabel) (i : Fin 3),
    R.readout () l i = (labelWindow l).val i

theorem window_rejected_law : ¬ windowArena.Law windowRejected := by
  intro h
  have impossible : true = false := h .L0 0
  exact Bool.noConfusion impossible

def windowRegistration : Registration windowArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.labelBit_window)) where
  actual := windowActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.labelBit_window,
    windowRejected, window_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨windowRejected, ?_, rfl, window_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Label.L2, 0, 1, ?_⟩
    change true ≠ false
    decide

def labelBit_window_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.labelBit_window)
      (type_of% (realize.{0,0,0,0,0} windowSignature (fun _ l i => labelBit l i.val) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.labelBit_window_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.windowRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} windowSignature (fun _ l i => labelBit l i.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms windowRegistration

def thirdActual : Realization bitSignature :=
  realize.{0,0,0,0,0} bitSignature (fun _ _ l => labelBit l 2) (fun e => nomatch e)
def thirdRejected : Realization bitSignature :=
  realize.{0,0,0,0,0} bitSignature (fun _ _ _ => true) (fun e => nomatch e)

abbrev thirdArena : Arena where
  signature := bitSignature
  Law R := ∀ (s : CGuard) (l : CLabel) (s' : CGuard)
    (h : nextGuard s l = some s'), R.readout () () l = guardBool s'

theorem third_rejected_law : ¬ thirdArena.Law thirdRejected := by
  intro h
  have impossible : true = false := h .G0 .L0 .G0 rfl
  exact Bool.noConfusion impossible

def thirdRegistration : Registration thirdArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.edge_third_guard)) where
  actual := thirdActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.edge_third_guard,
    thirdRejected, third_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨thirdRejected, ?_, rfl, third_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), Label.L0, Label.L5, ?_⟩
    change false ≠ true
    decide

def edge_third_guard_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.edge_third_guard)
      (type_of% (realize.{0,0,0,0,0} bitSignature (fun _ _ l => labelBit l 2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.edge_third_guard_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.thirdRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨thirdArena⟩
  objectArena := .source ⟨thirdArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thirdArena ⟨thirdRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} bitSignature (fun _ _ l => labelBit l 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms thirdRegistration

def firstActual : Realization bitSignature :=
  realize.{0,0,0,0,0} bitSignature (fun _ _ l => labelBit l 0) (fun e => nomatch e)
def firstRejected : Realization bitSignature :=
  realize.{0,0,0,0,0} bitSignature (fun _ _ _ => true) (fun e => nomatch e)

abbrev firstArena : Arena where
  signature := bitSignature
  Law R := ∀ (l : CLabel) (s' : CGuard)
    (h : nextGuard .G1 l = some s'), R.readout () () l = false

theorem first_rejected_law : ¬ firstArena.Law firstRejected := by
  intro h
  have impossible : true = false := h .L0 .G0 rfl
  exact Bool.noConfusion impossible

/-- Dependence ranges over typed labels. L2 has no G1 edge; the full Law
retains its edge hypothesis and makes no dependence claim within that hypothesis. -/
def firstRegistration : Registration firstArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.g1_edge_has_zero_first)) where
  actual := firstActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.g1_edge_has_zero_first,
    firstRejected, first_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨firstRejected, ?_, rfl, first_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), Label.L0, Label.L2, ?_⟩
    change false ≠ true
    decide

def g1_edge_has_zero_first_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.g1_edge_has_zero_first)
      (type_of% (realize.{0,0,0,0,0} bitSignature (fun _ _ l => labelBit l 0) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.g1_edge_has_zero_first_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.firstRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨firstArena⟩
  objectArena := .source ⟨firstArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source firstArena ⟨firstRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} bitSignature (fun _ _ l => labelBit l 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms firstRegistration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.ExactOriginal210
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ → CLabel
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ a j => rawDigits a j) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => true) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (a : ℕ → CLabel) (path : ℕ → CGuard)
      (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p+1))),
      ∀ j, ¬ (r.readout () a j = true ∧ rawDigits a (j+1) = true)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h (fun _ => Label.L3) (fun _ => Guard.G0) (fun _ => rfl) 0
  exact impossible ⟨rfl, rfl⟩

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_legal_of_operation_edges) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_legal_of_operation_edges, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(fun _ => Label.L3), 0, 1, ?_⟩
    change false ≠ true
    decide

def rawDigits_legal_of_operation_edges_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_legal_of_operation_edges)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ a j => rawDigits a j) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.ExactOriginal210.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.ExactOriginal210.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ a j => rawDigits a j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms rawDigits_legal_of_operation_edges_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.ExactOriginal210
