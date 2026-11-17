import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
import Reg.Support.SingleDependentReadout

/-! Source-bound four-slot audit attempts for the scalar formula and squeezing laws. -/

namespace Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar

open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p k => value k p.1 p.2.1 p.2.2) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1⟩, 1, 2, ?_⟩
  have h := (parameter_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)
  exact ne_of_gt h

abbrev quotientArena : Arena where
  signature := signature
  Law R := ∀ k x y z : ℝ, 0 ≤ k → 0 ≤ x → 0 ≤ y → 0 ≤ z →
    R.readout () ⟨x, y, z⟩ k =
      Real.log ((1 + k * pairSum x y z) ^ 2 /
        (cut k x y z * cut k y x z * cut k z x y)) / 12

private theorem quotient_rejected : ¬ quotientArena.Law oneReadout := by
  intro h
  have he := h 0 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [oneReadout, realize, cut] at he

def quotientFamily : Registration quotientArena (type_of% @value_eq_log_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨value_eq_log_ratio, oneReadout, quotient_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    quotientArena.Law actual oneReadout quotient_rejected
  dependence := actual_dependence

abbrev negativeArena : Arena where
  signature := signature
  Law R := ∀ k x y z : ℝ, 0 < k → 0 < x → 0 < y → 0 < z →
    R.readout () ⟨x, y, z⟩ k < 0

private theorem negative_rejected : ¬ negativeArena.Law zeroReadout := by
  intro h
  have he := h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [zeroReadout, realize] at he

def negativeFamily : Registration negativeArena (type_of% @value_neg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨value_neg, zeroReadout, negative_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    negativeArena.Law actual zeroReadout negative_rejected
  dependence := actual_dependence

abbrev parameterArena : Arena where
  signature := signature
  Law R := ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
    value 0 x y z = 0 ∧ StrictAntiOn (R.readout () ⟨x, y, z⟩) (Set.Ici 0)

private theorem parameter_rejected : ¬ parameterArena.Law zeroReadout := by
  intro h
  have he := (h 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2
    (show (0 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)
  norm_num [zeroReadout, realize] at he

def parameterFamily : Registration parameterArena (type_of% @parameter_behavior) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parameter_behavior, zeroReadout, parameter_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    parameterArena.Law actual zeroReadout parameter_rejected
  dependence := actual_dependence

def quotientAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@value_eq_log_ratio) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.quotientUnit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.quotientFamily
  realizationSource := none
  generated := false
  arena := .source ⟨quotientArena⟩
  objectArena := .source ⟨quotientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotientArena ⟨quotientFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k p.1 p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def negativeAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@value_neg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.negativeUnit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.negativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨negativeArena⟩
  objectArena := .source ⟨negativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source negativeArena ⟨negativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k p.1 p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def parameterAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parameter_behavior) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.parameterUnit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.parameterFamily
  realizationSource := none
  generated := false
  arena := .source ⟨parameterArena⟩
  objectArena := .source ⟨parameterArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source parameterArena ⟨parameterFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k p.1 p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms quotientAudit
#print axioms negativeAudit
#print axioms parameterAudit

abbrev swapArena : Arena where
  signature := signature
  Law R := ∀ k x y z : ℝ, R.readout () ⟨x,y,z⟩ k = value k y x z
private theorem swap_rejected : ¬ swapArena.Law oneReadout := by
  intro h
  have he := h 0 1 1 1
  norm_num [oneReadout, realize, value, cut] at he

def swapFamily : Registration swapArena (type_of% @value_swap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨value_swap, oneReadout, swap_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    swapArena.Law actual oneReadout swap_rejected
  dependence := actual_dependence

def swapAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@value_swap) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.swapUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.swapFamily
  realizationSource := none
  generated := false
  arena := .source ⟨swapArena⟩
  objectArena := .source ⟨swapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source swapArena ⟨swapFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k p.1 p.2.1 p.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
    definition := none
    coordinates := #[1,2,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms swapAudit

abbrev cycleArena : Arena where
  signature := signature
  Law R := ∀ k x y z : ℝ, R.readout () ⟨x,y,z⟩ k = value k y z x
private theorem cycle_rejected : ¬ cycleArena.Law oneReadout := by
  intro h
  have he := h 0 1 1 1
  norm_num [oneReadout, realize, value, cut] at he

def cycleFamily : Registration cycleArena (type_of% @value_cycle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨value_cycle, oneReadout, cycle_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    cycleArena.Law actual oneReadout cycle_rejected
  dependence := actual_dependence

def cycleAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@value_cycle) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.cycleUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.cycleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cycleArena⟩
  objectArena := .source ⟨cycleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cycleArena ⟨cycleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => value k p.1 p.2.1 p.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
    definition := none
    coordinates := #[1,2,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms cycleAudit

end
end Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
