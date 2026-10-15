import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeConstructorArrays
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open Observer.NativeConstructorArrays
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : Nat, Address
  State _ := Address → Reply
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => Observer.NativeConstructorArrays.realize p.1 z p.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Nat) (z : Address → Reply) (a : Address),
    Edges d z a → (0 < d → z a ≠ .absent) →
    Canonical d (R.readout false ⟨d,a⟩ z) ∧
      ∀ w : Address, w.length < d → readout w (R.readout true ⟨d,a⟩ z) = z (a ++ w)

private theorem positive : arena.Law actual := legal_realization

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 (fun _ => .branch) []
    (by intro w b hw; simp at hw)
    (by intro _; decide)).2 [] (by decide)
  change Reply.alpha = Reply.branch at bad
  cases bad

def canonicalRejected : Realization signature :=
  realize signature (fun i p z => if i then actual.readout i p z else .of false)
    (fun e => nomatch e)

private theorem canonicalNegative : ¬ arena.Law canonicalRejected := by
  intro h
  have bad := (h 0 (fun _ => .absent) []
    (by intro w b hw; omega) (by intro hd; omega)).1
  change (FreeMagma.of false : Source) = .of true at bad
  cases bad

def repliesRejected : Realization signature :=
  realize signature (fun i p z => if i then .of true else actual.readout i p z)
    (fun e => nomatch e)

private theorem repliesNegative : ¬ arena.Law repliesRejected := by
  intro h
  have bad := (h 1 (fun _ => .branch) []
    (by intro w b hw; simp at hw) (by intro _; decide)).2 [] (by decide)
  change Reply.alpha = Reply.branch at bad
  cases bad

def evidence : Registration arena (type_of% (@legal_realization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive,rejected,negative⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      · refine ⟨canonicalRejected, ?_, rfl, canonicalNegative⟩
        intro j h
        cases j
        · exact (h rfl).elim
        · rfl
      · refine ⟨repliesRejected, ?_, rfl, repliesNegative⟩
        intro j h
        cases j
        · rfl
        · exact (h rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,[]⟩, (fun _ => .alpha), (fun _ => .beta), ?_⟩
    change (FreeMagma.of true : Source) ≠ .of false
    intro h
    cases h

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@legal_realization) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays.legal_realization.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeConstructorArrays
    definition := none
    coordinates := #[0,2]
    readouts := #[
      { path := #["body","body","body","body","body","fn","arg","arg"]
        stateBinder := 0, functionOperand := false
        stateOperand := some #["fn","arg"], booleanPredicate := false },
      { path := #["body","body","body","body","body","arg","body","body","fn","arg","arg"]
        stateBinder := 0, functionOperand := false
        stateOperand := some #["fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev wholeSignature := Reg.Support.SingleDependentReadout.signature
  (Σ d : Nat, W d) (fun _ => Source) (fun _ => Reply)

def alphaState (p : {d : Nat // 0 < d}) : S p.val :=
  ⟨.of true, by
    cases h : p.val with
    | zero => have := p.property; omega
    | succ d => trivial⟩

def wholeActual : Realization wholeSignature :=
  realize wholeSignature (fun _ p t => readout p.2.val t) (fun e => nomatch e)

def wholeRejected : Realization wholeSignature :=
  realize wholeSignature (fun _ _ _ => .absent) (fun e => nomatch e)

abbrev wholeArena : Arena where
  signature := wholeSignature
  Law R := ∀ (d n : Nat) (hd : 0 < d) (hn : 0 < n),
    (∀ t : Source, Canonical 1 t ↔
      t = .of true ∨ t = .of false ∨ t = .mul (.of true) (.of true)) ∧
    (∀ (k : Nat) (l r : Source), Canonical (k+1) (.mul l r) ↔
      Canonical k l ∧ Canonical k r) ∧
    Function.Bijective (scalarReadout d hd) ∧
    Function.Bijective (productEquiv d n hd) ∧
    (∀ (x : Fin n → S d) (i : Fin n) (w : W d),
      (productEquiv d n hd x i).val w = R.readout () ⟨d,w⟩ (x i).val) ∧
    Fintype.card (Fin n × W d) = n * (2^d-1) ∧ Fintype.card Reply = 4

private theorem wholePositive : wholeArena.Law wholeActual :=
  faithful_constructor_representation

private theorem wholeNegative : ¬ wholeArena.Law wholeRejected := by
  intro h
  have bad := (h 1 1 (by decide) (by decide)).2.2.2.2.1
    (fun _ => alphaState ⟨1,by decide⟩) ⟨0,by decide⟩ ⟨[],by decide⟩
  change Reply.alpha = Reply.absent at bad
  cases bad

def wholeEvidence : Registration wholeArena
    (type_of% (@faithful_constructor_representation)) where
  actual := wholeActual
  bridge := Iff.rfl
  variation := ⟨wholePositive,wholeRejected,wholeNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ wholeNegative
  dependence := by
    intro i
    refine ⟨⟨1,⟨[],by decide⟩⟩, .of true, .of false, ?_⟩
    intro eq
    change Reply.alpha = Reply.beta at eq
    cases eq

def wholeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@faithful_constructor_representation) (Realization wholeSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays.faithful_constructor_representation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays.wholeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨wholeArena⟩
  objectArena := .source ⟨wholeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wholeArena ⟨wholeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wholeSignature wholeActual.readout wholeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeConstructorArrays
    definition := none
    coordinates := #[0,6]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","arg","arg","fn","arg",
        "body","body","body","arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms wholeEvidence
#print axioms wholeRegistration

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeConstructorArrays
