import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
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

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal138
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ T => 3^(T+1)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (T : ℕ), Finite (FactorDictionary X T) ∧ factorCount X T ≤ r.readout () () T

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let X : Set (ℤ → CuLetter) := {fun _ => .u}
  letI : Nonempty (FactorDictionary X 0) := ⟨⟨[], ⟨(fun _ => .u), rfl, 0, (by intro k; exact Fin.elim0 k)⟩, rfl⟩⟩
  letI : Finite (FactorDictionary X 0) := (h X 0).1
  have positive := Nat.card_pos (α := FactorDictionary X 0)
  have bound := (h X 0).2
  change Nat.card (FactorDictionary X 0) ≤ 0 at bound
  omega

def evidence : Registration sourceArena (type_of% @factor_dictionary_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@factor_dictionary_bound, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def factor_dictionary_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.factor_dictionary_bound)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ T => 3^(T+1)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal138.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal138.evidence
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
    (fun _ _ T => 3^(T+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms factor_dictionary_bound_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal138

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal141
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℤ → CuLetter
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => .c) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (W : ℤ → List CuLetter) (positive : ∀ j, 0 < (W j).length) (ω : ℤ → CuLetter)
    (tiles : ∀ j (k : Fin (W j).length), ω (blockCut W j + (k : ℕ)) = (W j)[k])
    (a : ℤ) (q : ℕ), ∀ k : Fin (blockWindow W a q).length,
    r.readout () ω (blockCut W a + (k : ℕ)) = (blockWindow W a q)[k]

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have tiles : ∀ j (k : Fin ([CuLetter.u] : List CuLetter).length),
      (fun _ : ℤ => CuLetter.u) (blockCut (fun _ => [.u]) j + (k : ℕ)) =
        ([CuLetter.u] : List CuLetter)[k] := by
    intro j k
    have hk : k.val = 0 := congrArg Fin.val (Fin.eq_zero k)
    simp [hk]
  have impossible := h (fun _ => [.u]) (by intro j; simp) (fun _ => .u) tiles 0 1
    ⟨0, by simp [blockWindow]⟩
  simp [rejected, realize, blockWindow] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.tiled_window_occurs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.tiled_window_occurs, rejected, rejected_law⟩
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
    refine ⟨(fun x => if x = 0 then .u else .c), 0, 1, ?_⟩
    simp [actual, realize]

def tiled_window_occurs_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.tiled_window_occurs)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal141.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal141.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms tiled_window_occurs_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal141

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal142
noncomputable section
universe u_1
abbrev observationSignature : Signature.{u_1+1,0,0,u_1,0} where
  Params := Σ (V : Type u_1), Σ _ : ℤ → V, ℤ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature.{u_1} := realize.{u_1+1,0,0,u_1,0} observationSignature (fun _ p q => @choiceWindow p.1 p.2.1 p.2.2 q) (fun e => nomatch e)
def rejected : Realization observationSignature.{u_1} :=
  realize observationSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev sourceArena : Arena.{u_1+1,0,0,u_1,0} where
  signature := observationSignature
  Law r := ∀ {V : Type u_1} (choices : ℤ → V) (a : ℤ) (q : ℕ),
    r.readout () ⟨V, ⟨choices, a⟩⟩ q = List.ofFn (fun i : Fin q => choices (a+(i : ℕ)))

theorem rejected_law : ¬ sourceArena.{u_1}.Law rejected := by
  intro h
  have impossible := h (V := PUnit.{u_1+1}) (fun _ => PUnit.unit) 0 1
  have lengths := congrArg List.length impossible
  simpa [rejected, realize] using lengths

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.choice_window_ofFn.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.choice_window_ofFn.{u_1}, rejected, rejected_law⟩
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
    refine ⟨⟨PUnit.{u_1+1}, ⟨(fun _ => PUnit.unit), 0⟩⟩, 0, 1, ?_⟩
    simp [actual, realize, choiceWindow]

def choice_window_ofFn_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,u_1+1,0,0,u_1,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.choice_window_ofFn.{u_1})
      (type_of% (realize.{u_1+1,0,0,u_1,0} observationSignature (fun _ p q => @choiceWindow p.1 p.2.1 p.2.2 q) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal142.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal142.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{u_1+1,0,0,u_1,0} observationSignature (fun _ p q => @choiceWindow p.1 p.2.1 p.2.2 q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms choice_window_ofFn_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal142

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.RateWitness
noncomputable section

theorem actual_rate_separation :
    weightedFactorRate (MemoryLanguage .lower 1 1 (oneStepCeiling + 1)) ≠
      weightedFactorRate (MemoryLanguage .lower 0 2 0) := by
  have zero := (original_closed_root_boundary .lower (oneStepCeiling + 1)
    (lt_add_one _)).2.2.2
  have positive := original_positive_weighted_rate .lower 0 2 0 (by norm_num)
  rw [zero]
  intro equal
  rw [← equal] at positive
  norm_num at positive

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.RateWitness


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal143
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Set (ℤ → CuLetter)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (a L : ℕ) (positive : 0 < L) (counts : ∀ q, a^q ≤ factorCount X (q*L)), Real.logb 2 ((max 1 a : ℕ) : ℝ) / (L : ℝ) ≤ r.readout () () X

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h (MemoryLanguage .lower 0 2 0) 2 58 (by norm_num)
    (original_literal_codebook_growth .lower 0 2 0 (by norm_num))
  norm_num [rejected, realize, Real.logb_self_eq_one] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.factor_rate_of_power_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.factor_rate_of_power_count, rejected, rejected_law⟩
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
    refine ⟨(), MemoryLanguage .lower 1 1 (oneStepCeiling + 1),
      MemoryLanguage .lower 0 2 0, ?_⟩
    exact Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.RateWitness.actual_rate_separation

def factor_rate_of_power_count_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.factor_rate_of_power_count)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal143.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal143.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms factor_rate_of_power_count_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal143


open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budgetLower budget budget_interval)
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
  (rejected reset_floor_rejected)

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal144
noncomputable section

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g^2*chi^K*hSide .high < b)
    (hbp : b < lam - g^2*chi^K*(aSide .high/(1-rho*chi^K))),
    ∃ R : Return, R.r = 1 ∧
    (max (max (xSide .high) (ySide .high))
      ((lam-r.readout () () b)/g^2/chi^K) <
      hSide .high-rho^R.m*(hSide .high-chi*aSide .high)) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam-b)/g^2/chi^K
    let delta := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)-initial .high sourceModel
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    let L := N+20+6*R.m
    0 < delta ∧ 0 < delta*g^N ∧
    0 < min (b-actualAutomaticCost K) (g^2*chi^K*(delta*g^N))/2 ∧ Finite V ∧
    (∀ (targetModel : Model) (words : List V),
      let execution := resetConcatenation R (words.map Subtype.val)
      GuardTrace K (d+delta*g^N) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o
        (b-min (b-actualAutomaticCost K) (g^2*chi^K*(delta*g^N))/2) .strict execution) ∧
    ∃ n : ℕ, K ≤ n ∧ hSide .high*rho^n < chi^(K-1)*(delta*g^N) ∧
      (∀ choices : ℤ → V,
        let W := fun j => executionWord (R::(choices j).val)
        ∃ ω : ℤ → CuLetter,
          ω ∈ AuxiliaryLanguage K (d+delta*g^N) ∧ ω ∈ LowerMemoryLanguage n K d ∧
          (∀ j (k : Fin (W j).length), ω (blockCut W j+(k : ℕ))=(W j)[k]) ∧
          (∀ j, GuardTrace K (d+delta*g^N) false .high (R::(choices j).val)
            (pastState ω (blockCut W j)))) ∧
      (∀ q : ℕ,
        let f := fun z : Fin q → V => resetFactor R (List.ofFn (fun i => (z i).val))
        Function.Injective f ∧
        (∀ z, wordWeight (f z) = q*L ∧
          ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω (f z)) ∧
        (∃ family : Finset (List CuLetter), family.card = Nat.card V^q ∧
          (∀ w, w ∈ family ↔ ∃ z, f z = w) ∧
          (∀ w ∈ family, wordWeight w = q*L ∧
            ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω w)) ∧
        Nat.card V^q ≤ factorCount (LowerMemoryLanguage n K d) (q*L)) ∧
      Real.logb 2 ((max 1 (Nat.card V) : ℕ) : ℝ)/(L : ℝ) ≤
        weightedFactorRate (LowerMemoryLanguage n K d)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => budgetLower) (fun e => nomatch e)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, _, floor, _⟩ :=
    h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2
  exact reset_floor_rejected R floor

def evidence : Registration sourceArena
    (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.same_reset_factor_cardinality) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.same_reset_factor_cardinality,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def same_reset_factor_cardinality_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.same_reset_factor_cardinality)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal144.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal144.evidence
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
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms same_reset_factor_cardinality_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.ExactOriginal144
