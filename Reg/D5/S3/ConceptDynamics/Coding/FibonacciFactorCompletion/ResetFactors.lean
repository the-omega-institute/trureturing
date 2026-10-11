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

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.Injection
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

abbrev concatSignature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State L := List {w : List CuLetter // wordWeight w = L}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def concatActual : Realization concatSignature :=
  realize concatSignature (fun _ _ words => (words.map Subtype.val).flatten)
    (fun e => nomatch e)
def concatRejected : Realization concatSignature :=
  realize concatSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev concatArena : Arena.{0,0,0,0,0} where
  signature := concatSignature
  Law r := ∀ (L : ℕ) (positive : 0 < L), Function.Injective (r.readout () L)

private def uBlock : {w : List CuLetter // wordWeight w = 6} := ⟨[.u], rfl⟩
private theorem concat_bad : ¬ concatArena.Law concatRejected := by
  intro h
  have eq : ([] : List {w : List CuLetter // wordWeight w = 6}) = [uBlock] :=
    h 6 (by decide) rfl
  cases eq

def concatRegistration : Registration concatArena (type_of% @equal_weight_concatenation_injective) where
  actual := concatActual
  bridge := Iff.rfl
  variation := ⟨@equal_weight_concatenation_injective, concatRejected, concat_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨concatRejected, ?_, rfl, concat_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨6, [], [uBlock], ?_⟩
    simp [concatActual, realize, uBlock]

def equal_weight_concatenation_injective_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.equal_weight_concatenation_injective)
      (type_of% (realize.{0,0,0,0,0} concatSignature
        (fun _ _ words => (words.map Subtype.val).flatten) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.Injection.concat_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.Injection.concatRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨concatArena⟩
  objectArena := .source ⟨concatArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source concatArena ⟨concatRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} concatSignature
        (fun _ _ words => (words.map Subtype.val).flatten) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms concatRegistration
#print axioms equal_weight_concatenation_injective_registration

abbrev resetSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Return, Σ _ : ℕ, (List Return → Prop)
  State q := List {xs : List Return // q.2.2 xs ∧ listWeight xs = q.2.1}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def resetActual : Realization resetSignature :=
  realize resetSignature (fun _ q words => resetFactor q.1 (words.map Subtype.val))
    (fun e => nomatch e)
def resetRejected : Realization resetSignature :=
  realize resetSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev resetArena : Arena.{0,0,0,0,0} where
  signature := resetSignature
  Law r := ∀ (R : Return) (N : ℕ) (p : List Return → Prop),
    Function.Injective (r.readout () ⟨R, ⟨N, p⟩⟩) ∧
    ∀ words : List {xs : List Return // p xs ∧ listWeight xs = N},
      wordWeight (resetFactor R (words.map Subtype.val)) =
        words.length * (N + 20 * R.r + 6 * R.m)

private def return11 : Return := ⟨1, 1, by decide, by decide⟩
private def emptyReturnBlock : {xs : List Return // True ∧ listWeight xs = 0} :=
  ⟨[], trivial, rfl⟩
private theorem reset_bad : ¬ resetArena.Law resetRejected := by
  intro h
  have eq : ([] : List {xs : List Return // True ∧ listWeight xs = 0}) =
      [emptyReturnBlock] := (h return11 0 (fun _ => True)).1 rfl
  cases eq

def resetRegistration : Registration resetArena (type_of% @reset_factor_parser) where
  actual := resetActual
  bridge := Iff.rfl
  variation := ⟨@reset_factor_parser, resetRejected, reset_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨resetRejected, ?_, rfl, reset_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨return11, ⟨0, (fun _ => True)⟩⟩, [], [emptyReturnBlock], ?_⟩
    simp [resetActual, realize, resetFactor, executionWord, return11, emptyReturnBlock]

def reset_factor_parser_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.reset_factor_parser)
      (type_of% (realize.{0,0,0,0,0} resetSignature
        (fun _ q words => resetFactor q.1 (words.map Subtype.val)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.Injection.reset_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.Injection.resetRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨resetArena⟩
  objectArena := .source ⟨resetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resetArena ⟨resetRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} resetSignature
    (fun _ q words => resetFactor q.1 (words.map Subtype.val)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms resetRegistration
#print axioms reset_factor_parser_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.Injection
