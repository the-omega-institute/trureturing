import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge
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
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.labelBit_window_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.windowRegistration
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
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
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.edge_third_guard_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.thirdRegistration
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
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
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.g1_edge_has_zero_first_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.firstRegistration
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
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
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal210
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
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal210.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal210.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
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
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal210

open _root_.D5.S1.Digit.Infinite.SuccessorContinuity
open _root_.D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal212
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ → CLabel
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => CLabel
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ a p => a p) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L2) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (a : ℕ → CLabel) (path : ℕ → CGuard)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1))),
    let d : LegalDigits := ⟨rawDigits a, rawDigits_legal_of_operation_edges a path hedges⟩
    ∀ p, window d p = labelWindow (r.readout () a p)


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let a : ℕ → CLabel := fun _ => .L0
  let path : ℕ → CGuard := fun _ => .G0
  have hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)) := fun _ => rfl
  have good := D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_window a path hedges 0
  have bad := h a path hedges 0
  have impossible := good.symm.trans bad
  have bit := congrArg (fun l : SLabel => l.val (0 : Fin 3)) impossible
  change false = true at bit
  exact Bool.noConfusion bit

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_window) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_window, rejected, rejected_law⟩
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
    refine ⟨(fun n => if n = 0 then _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L0 else .L2), 0, 1, ?_⟩
    change _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L0 ≠ _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L2
    decide

def rawDigits_window_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.rawDigits_window)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ a p => a p) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal212.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal212.evidence
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
    (fun _ a p => a p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms rawDigits_window_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal212

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal214
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ → ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ x p => x p) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (a : ℕ → CLabel) (x : ℕ → ℝ)
    (h : OperationOmega a x),
    ∃ d : LegalDigits, ∃ path : ℕ → CGuard,
      path 0 = .G0 ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, window d p = labelWindow (a p)) ∧
      (∀ p, actualGuard false d p = guardBool (path p)) ∧
      (∀ p, x p ∈ D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.stateInterval
        (guardBool (path p))) ∧
      (∀ p, r.readout () x p = D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.branch
        (labelWindow (a p)) (x (p + 1)))


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have premise : OperationOmega (fun _ => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L0) (fun _ => (0 : ℝ)) := by
    refine ⟨(fun _ => .G0), rfl, (fun _ => rfl), ?_, ?_⟩
    · intro p
      constructor
      · norm_num
      · dsimp [supportUpper, phi,
          D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.t]
        have hs0 := Real.sqrt_nonneg (5 : ℝ)
        linarith
    · intro p
      simp [D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch, shift]
  obtain ⟨d, path, hall⟩ := h (fun _ => .L0) (fun _ => 0) premise
  have impossible := hall.2.2.2.2.2 0
  change (1 : ℝ) = D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.branch (labelWindow .L0) 0 at impossible
  rw [branch_transport] at impossible
  simp [D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch, shift] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.operation_digit_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.operation_digit_bridge, rejected, rejected_law⟩
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
    refine ⟨(fun n => (n : ℝ)), 0, 1, ?_⟩
    norm_num [actual, realize]

def operation_digit_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.operation_digit_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ x p => x p) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal214.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal214.evidence
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
    (fun _ x p => x p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms operation_digit_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal214

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal215
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ → CLabel
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ → CLabel
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ a => a) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => fun _ => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L3) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (a : ℕ → CLabel) (d : LegalDigits)
    (hw : ∀ p, window d p = labelWindow (a p)),
    OperationFiniteSource (r.readout () () a) ↔ finiteTail d


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let d : LegalDigits := ⟨(fun _ => false), by simp⟩
  have hw : ∀ p, window d p = labelWindow ((fun _ => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L0) p) := by
    intro p
    apply Subtype.ext
    funext i
    rfl
  have ht : finiteTail d := ⟨0, fun _ _ => rfl⟩
  obtain ⟨M, hM⟩ := (h (fun _ => .L0) d hw).mpr ht
  have impossible := hM M (Nat.le_refl M)
  change _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L3 = _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L0 at impossible
  exact Label.noConfusion impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.operation_finite_source_iff_of_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.operation_finite_source_iff_of_bridge, rejected, rejected_law⟩
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
    refine ⟨(), (fun _ => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L0), (fun _ => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.Label.L3), ?_⟩
    intro h
    have impossible := congrFun h 0
    exact Label.noConfusion impossible

def operation_finite_source_iff_of_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.operation_finite_source_iff_of_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ a => a) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal215.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal215.evidence
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
    (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms operation_finite_source_iff_of_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal215

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal213
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature CLabel (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ l y => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch l y) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (l : CLabel) (y : ℝ),
    _root_.D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel.branch
      (labelWindow l) y = r.readout () l y

theorem source_bridge : (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.branch_transport) ↔
    sourceArena.Law actual := Iff.rfl

theorem positive_law : sourceArena.Law actual := @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.branch_transport

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h Label.L0 0
  rw [_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.branch_transport] at impossible
  norm_num [rejected, realize, _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch, _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.shift] at impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨Label.L0, 0, 1, ?_⟩
  have hgp : 0 < _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.g :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.tail_arithmetic.2.2.2.1
  change _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch Label.L0 0 ≠ _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch Label.L0 1
  simp only [_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch, _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.shift]
  intro impossible
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.branch_transport) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

def branch_transport_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge.branch_transport)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ l y => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch l y) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal213.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal213.evidence
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
    (fun _ l y => _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch l y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms branch_transport_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.Bridge.ExactOriginal213

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
open _root_.D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open _root_.D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates

noncomputable section

abbrev coordinateSignature : Signature where
  Params := Σ _ : ℕ → CLabel, ℕ → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateActual : Realization coordinateSignature :=
  realize coordinateSignature (fun _ params p => params.2 p) (fun e => nomatch e)

def coordinateRejected : Realization coordinateSignature :=
  realize coordinateSignature (fun _ params p => params.2 p + 1) (fun e => nomatch e)

abbrev coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ (a : ℕ → CLabel) (x : ℕ → ℝ), OperationOmega a x →
    ∃ d : LegalDigits,
      (∀ p, window d p = labelWindow (a p)) ∧
      (∀ p, R.readout () ⟨a, x⟩ p = kappa (bitShift d (3 * p))) ∧
      (OperationFiniteSource a ↔ finiteTail d)

theorem coordinate_rejected_law : ¬ coordinateArena.Law coordinateRejected := by
  intro h
  have hzero : OperationOmega
      (_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.address [])
      (_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate []) :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_address_path
      .G0 .G0 [] rfl
  obtain ⟨d, hw, hc, _⟩ := h _ _ hzero
  have hwindow : ∀ p, window d p = nullLabel := by
    intro p
    simpa [_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.address,
      labelWindow] using hw p
  have hk : kappa d = 0 := by simp [kappa, hwindow, offset, nullLabel]
  have hvalue := hc 0
  simp [coordinateRejected, realize, bitShift,
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate,
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.compose] at hvalue
  exact one_ne_zero (hvalue.trans hk)

def coordinateRegistration : Registration coordinateArena
    (∀ (a : ℕ → CLabel) (x : ℕ → ℝ), OperationOmega a x →
      ∃ d : LegalDigits, (∀ p, window d p = labelWindow (a p)) ∧
        (∀ p, x p = kappa (bitShift d (3 * p))) ∧
        (OperationFiniteSource a ↔ finiteTail d)) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨operation_coordinate_bridge, coordinateRejected, coordinate_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected, ?_, rfl, coordinate_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.address [.L2],
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate [.L2]⟩,
      0, 1, ?_⟩
    norm_num [coordinateActual, realize,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.coordinate,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.compose,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.branch,
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.shift]

def operation_coordinate_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.operation_coordinate_bridge)
      (type_of% (realize.{0,0,0,0,0} coordinateSignature
        (fun _ params p => params.2 p) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.operation_coordinate_bridge_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates.coordinateRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨coordinateArena⟩
  objectArena := .source ⟨coordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coordinateArena ⟨coordinateRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} coordinateSignature
    (fun _ params p => params.2 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
