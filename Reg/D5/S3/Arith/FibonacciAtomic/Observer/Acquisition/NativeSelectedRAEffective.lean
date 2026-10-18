import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution (EffectiveProgram Run Word)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective

abbrev codingSignature : Signature where
  Params := Unit
  State _ := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def codingActual : Realization codingSignature :=
  realize codingSignature (fun _ _ s => encodeState s) (fun i => nomatch i)

def codingBad : Realization codingSignature :=
  realize codingSignature (fun _ _ _ => 0) (fun i => nomatch i)

private theorem code_dependence : ObservationalDependence codingSignature codingActual := by
  intro i
  refine ⟨(),.entry,.ready true [],?_⟩
  intro same
  have no := effective_selected_machine.1 same
  cases no

abbrev codingArena : Arena where
  signature := codingSignature
  Law R := Function.Injective (R.readout () ()) ∧
    ∃ P : EffectiveProgram, ∀ s : State,
      P.transition (encodeState s) = encodedOp (step s)

private theorem coding_bad : ¬ codingArena.Law codingBad := by
  intro h
  have no := h.1 (a₁ := State.entry) (a₂ := State.ready true []) rfl
  cases no

def codingProof : Registration codingArena (type_of% (@effective_selected_machine)) where
  actual := codingActual
  bridge := Iff.rfl
  variation := ⟨@effective_selected_machine,codingBad,coding_bad⟩
  sensitivity := ⟨fun i => ⟨codingBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,coding_bad⟩,fun i => nomatch i⟩
  dependence := code_dependence

abbrev producerArena : Arena where
  signature := codingSignature
  Law R :=
    (Function.Injective (R.readout () ()) ∧
      ∃ P : EffectiveProgram, ∀ s : State,
        P.transition (encodeState s) = encodedOp (step s)) ∧
    (∀ (u : Source) (h : Word) (b : State), Run step .entry u h b →
      ∃ (q : Bool) (row : List Cell), b = .ready q row ∧
        Captured u (eventSchedule h) h.length q row) ∧
    (∀ (u : Source) (σ : Nat → Bool),
      Set.Finite {n : Nat | σ n = true ∧
        (trajectory σ ⟨.entry,u,false⟩ n).returned = false} →
      ∃ m : Nat, (trajectory σ ⟨.entry,u,false⟩ m).returned = true) ∧
    (∀ u : Source, (∃ h : Word, Run step .entry u h (.ready true rootBytes)) ↔ u = .of true) ∧
    (∀ (u : Source) (j : Nat),
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.literalRecord {[]}
        (substitution^[j] u) =
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.rootLabel)

private theorem producer_bad : ¬ producerArena.Law codingBad := by
  intro h
  exact coding_bad h.1

def producerProof : Registration producerArena (type_of% (@selected_producer_contract)) where
  actual := codingActual
  bridge := Iff.rfl
  variation := ⟨@selected_producer_contract,codingBad,producer_bad⟩
  sensitivity := ⟨fun i => ⟨codingBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,producer_bad⟩,fun i => nomatch i⟩
  dependence := code_dependence

noncomputable def effective_selected_machine_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective.effective_selected_machine) (Realization codingSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective.effective_selected_machine
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective.codingProof
  realizationSource := none
  generated := false
  arena := .source ⟨codingArena⟩
  objectArena := .source ⟨codingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source codingArena ⟨codingProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize codingSignature (fun _ _ s => encodeState s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def selected_producer_contract_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective.selected_producer_contract) (Realization codingSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective.selected_producer_contract
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective.producerProof
  realizationSource := none
  generated := false
  arena := .source ⟨producerArena⟩
  objectArena := .source ⟨producerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source producerArena ⟨producerProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize codingSignature (fun _ _ s => encodeState s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective
