import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
open _root_.D5.S3.Arith.FibonacciAtomic
open Observer.NativeActiveParityExecution (Control start endpoint dispatch next)
open Observer.NativeFibonacciActiveTable
open Observer
open Observer.NativeSerialMachine (Event nativeStep)
open Observer.NativeControlConjugacy
open ActualTreeReadoutAcquisition (Address Reply readout)
open GenealogicalFiberTransport (Source substitution)
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
abbrev tableSignature := Reg.Support.SingleDependentReadout.signature Nat
  (fun h => Control h) (fun h => Fin (dimension h+7) → Bool)
def tableActual : Realization tableSignature :=
  realize tableSignature (fun _ h => encode (path h)) (fun e => nomatch e)
def tableRejected : Realization tableSignature :=
  realize tableSignature (fun _ h _ => encode (path h) (start h)) (fun e => nomatch e)
abbrev tableArena : Arena where
  signature := tableSignature
  Law R := ∀ (h : Nat) (address : Fin h → Address) (K : Nat),
    h+1 ≤ Nat.fib (dimension h+2) ∧
    (∀ d, d < dimension h → Nat.fib (d+2) < h+1) ∧
    Function.Injective (R.readout () h) ∧
    (∀ c, Adm (dimension h+7) (encode (path h) c)) ∧
    Nat.card (Installed (path h)) = 8*h+8 ∧
    AllRows (path h) address K ∧
    Certificate (encodingEquiv (path h)) (nativeProgram address K) ∧
    (∀ (entry : Type) (initial : entry → Source) (target : entry → Bool) (c : Control h),
      EncodedSupport (path h) address K entry initial target (encodingEquiv (path h) c) =
        Support address K entry initial target c) ∧
    (∀ c j u n a, FirstHalt (encodedProgram (path h) address K)
      (encodingEquiv (path h) c) j u n a ↔ FirstHalt (nativeProgram address K) c j u n a) ∧
    RankDescent (path h) address K

private theorem tableNegative : ¬ tableArena.Law tableRejected := by
  intro law
  have injective := (law 0 Fin.elim0 0).2.2.1
  have same := injective (a₁ := start 0) (a₂ := endpoint 0 true) rfl
  have impossible := congrArg _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.accumulator same
  change false = true at impossible
  cases impossible

def tableEvidence : Registration tableArena (type_of% (@native_fibonacci_active_table)) where
  actual := tableActual
  bridge := Iff.rfl
  variation := ⟨native_fibonacci_active_table, tableRejected, tableNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ tableNegative
  dependence := by
    intro i
    refine ⟨0, start 0, endpoint 0 true, ?_⟩
    intro same
    have bit := congrFun same ((1 : Fin 7).natAdd (dimension 0))
    simp [tableActual, realize, encode, suffix, accumulator, start, endpoint] at bit

def table : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_fibonacci_active_table) (Realization tableSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.native_fibonacci_active_table.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.tableEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨tableArena⟩
  objectArena := .source ⟨tableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tableArena ⟨tableEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tableSignature tableActual.readout tableActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","body","arg","arg","fn","arg","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev executionSignature := Reg.Support.SingleDependentReadout.signature Source
  (fun S => Fin S.length → Bool) (fun _ => Source)
def executionActual : Realization executionSignature :=
  realize executionSignature (fun _ S x => Observer.NativeActiveParityExecution.source
    (Observer.NativeActiveParityExecution.chartOf S) x) (fun e => nomatch e)
def executionRejected : Realization executionSignature :=
  realize executionSignature (fun _ _ _ => (.of true : Source)) (fun e => nomatch e)
abbrev executionArena : Arena where
  signature := executionSignature
  Law R := ∀ (S : Source) (x : Fin S.length → Bool) (t K : Nat),
    t ≤ 2*K → (S.length % 2 = 0 ∨ t = 0) →
    ∃ trace, NativeSerialMachine.Run
        (nativeProgram (Observer.NativeActiveParityExecution.chartOf S).address K)
        (start S.length) 0
        (substitution^[t] ((R.readout () S x)))
        trace (Observer.NativeActiveParityExecution.parity (Observer.NativeActiveParityExecution.labels x) S.length) ∧
      NativeSerialMachine.Run
        (encodedProgram (path S.length) (Observer.NativeActiveParityExecution.chartOf S).address K)
        (encodingEquiv (path S.length) (start S.length)) 0
        (substitution^[t] (Observer.NativeActiveParityExecution.source (Observer.NativeActiveParityExecution.chartOf S) x))
        trace (Observer.NativeActiveParityExecution.parity (Observer.NativeActiveParityExecution.labels x) S.length) ∧
      FirstHalt (nativeProgram (Observer.NativeActiveParityExecution.chartOf S).address K)
        (start S.length) 0
        (substitution^[t] (Observer.NativeActiveParityExecution.source (Observer.NativeActiveParityExecution.chartOf S) x))
        trace.length (Observer.NativeActiveParityExecution.parity (Observer.NativeActiveParityExecution.labels x) S.length) ∧
      updates trace = 2*(K-(t+Observer.NativeActiveParityExecution.bit (x ⟨0,S.length_pos⟩))/2) ∧
      (∀ m : CostModel, cost m trace 0 = trace.length) ∧
      (∃ w J, StateTransition.Reaches
        (nativeStep (encodedProgram (path S.length) (Observer.NativeActiveParityExecution.chartOf S).address K))
        (encodingEquiv (path S.length) (start S.length),0,
          substitution^[t] (Observer.NativeActiveParityExecution.source (Observer.NativeActiveParityExecution.chartOf S) x),[])
        (w,J,substitution^[J] (substitution^[t]
          (Observer.NativeActiveParityExecution.source (Observer.NativeActiveParityExecution.chartOf S) x)),trace) ∧
        encodedProgram (path S.length) (Observer.NativeActiveParityExecution.chartOf S).address K w =
          .stop (Observer.NativeActiveParityExecution.parity (Observer.NativeActiveParityExecution.labels x) S.length) ∧
        ∀ n p y, Event.read n p y ∈ trace → readout p (substitution^[n] (substitution^[t]
          (Observer.NativeActiveParityExecution.source (Observer.NativeActiveParityExecution.chartOf S) x))) = y)

private theorem executionNegative : ¬ executionArena.Law executionRejected := by
  intro law
  let C := Observer.NativeActiveParityExecution.chartOf ((.of true : Source))
  let δ := nativeProgram C.address 0
  let index : Fin 1 := ⟨0,by decide⟩
  have forced : Observer.NativeSerialMachine.Run δ (start 1) 0 (.of true)
      [.read 0 [] .alpha,.read 0 [] .alpha,.read 0 [] .alpha] false := by
    apply Observer.NativeSerialMachine.Run.read (k := dispatch index false)
      (by simp [δ,nativeProgram,start,C,index,Observer.NativeActiveParityExecution.chartOf,
        Observer.NativeActiveParityExecution.locator,Observer.DelayedOriginalReadout.rights]) rfl
    change Observer.NativeSerialMachine.Run δ (.b index false false) 0 (.of true) _ false
    apply Observer.NativeSerialMachine.Run.read (k := fun _ => .c index false)
      (by simp [δ,nativeProgram]) rfl
    apply Observer.NativeSerialMachine.Run.read (k := fun _ => next index false) rfl rfl
    exact .stop (by simp [δ,nativeProgram,next,index])
  obtain ⟨trace,run,_⟩ := law (.of true) (fun _ => true) 0 0 (by decide) (Or.inr rfl)
  have wrong : Observer.NativeActiveParityExecution.parity
      (Observer.NativeActiveParityExecution.labels (fun _ : Fin 1 => true)) 1 = true := by
    simp [Observer.NativeActiveParityExecution.parity,Observer.NativeActiveParityExecution.labels]
  change Observer.NativeSerialMachine.Run δ (start 1) 0 (.of true) trace
    (Observer.NativeActiveParityExecution.parity (Observer.NativeActiveParityExecution.labels
      (fun _ : Fin 1 => true)) 1) at run
  rw [wrong] at run
  have impossible := (certificate (Equiv.refl (Control 1)) δ).deterministic
    (start 1) 0 (.of true) trace _ true false run forced
  cases impossible.2

def executionEvidence : Registration executionArena (type_of% (@encoded_active_parity_execution)) where
  actual := executionActual
  bridge := Iff.rfl
  variation := ⟨encoded_active_parity_execution, executionRejected, executionNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ executionNegative
  dependence := by
    intro i
    refine ⟨(.of true : Source), (fun _ => false), (fun _ => true), ?_⟩
    simp [executionActual, realize, Observer.NativeActiveParityExecution.source,
      Observer.NativeActiveParityExecution.chartOf, Observer.NativeActiveParityExecution.numbered,
      Observer.NativeActiveParityExecution.atom, Observer.NativeActiveParityExecution.bit,
      Observer.NativeActiveParityExecution.labels, ActualCutPartitionRecovery.evaluateRow,
      GenealogicalFiberTransport.substitution]
    intro same
    have raw := congrArg (readout []) same
    change Reply.alpha = Reply.beta at raw
    cases raw

def execution : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@encoded_active_parity_execution) (Realization executionSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.encoded_active_parity_execution.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.executionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨executionArena⟩
  objectArena := .source ⟨executionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source executionArena ⟨executionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize executionSignature executionActual.readout executionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","body","body","body","body","arg","body","fn","arg","fn","fn","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms executionEvidence
#print axioms execution

#print axioms tableEvidence
#print axioms table

abbrev firstSignature : Signature where
  Params := Type
  State C := C → Observer.NativeSerialMachine.Op C Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := C → Observer.NativeSerialMachine.Op C Bool
  Anchor := Empty
  finiteAnchor := inferInstance
def firstActual : Realization firstSignature :=
  realize firstSignature (fun _ _ δ => δ) (fun e => nomatch e)
def firstRejected : Realization firstSignature :=
  realize firstSignature (fun _ _ _ _ => .stop false) (fun e => nomatch e)
abbrev firstArena : Arena where
  signature := firstSignature
  Law R := ∀ {C : Type} (δ : C → Observer.NativeSerialMachine.Op C Bool)
    {c : C} {j : Nat} {u : Source} {trace : Observer.NativeSerialMachine.Trace} {a : Bool},
    Observer.NativeSerialMachine.Run δ c j u trace a →
      FirstHalt (R.readout () C δ) c j u trace.length a
private theorem firstNegative : ¬ firstArena.Law firstRejected := by
  intro law
  have fact := law (fun _ : Unit => Observer.NativeSerialMachine.Op.stop true)
    (c := ()) (j := 0) (u := .of true) (.stop rfl)
  obtain ⟨trace,run,_⟩ := fact.1
  cases run with
  | stop h => cases h
  | localStep h _ => cases h
  | update h _ => cases h
  | read h _ _ => cases h
def firstEvidence : Registration firstArena (type_of% (@first_of_run)) where
  actual := firstActual
  bridge := Iff.rfl
  variation := ⟨@first_of_run,firstRejected,firstNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨firstRejected,?_,?_,firstNegative⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨Unit,(fun _ => .stop false),(fun _ => .stop true),?_⟩
    intro same
    have bad := congrFun same ()
    cases bad

def firstRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@NativeFibonacciActiveTable.first_of_run) (Realization firstSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.first_of_run.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.firstEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨firstArena⟩
  objectArena := .source ⟨firstArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source firstArena ⟨firstEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize firstSignature firstActual.readout firstActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","fn","fn","fn","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms firstEvidence
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
