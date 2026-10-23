import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints (Formula)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution

abbrev signature : Signature where
  Params := Unit
  State _ := TimedWord
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Word
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => expand t) (fun i => nomatch i)

def bad : Realization signature :=
  realize signature (fun _ _ _ => []) (fun i => nomatch i)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), [], [(0,.ret)], ?_⟩
  simp [actual, realize, expand]

abbrev chronologicalArena : Arena where
  signature := signature
  Law R := ∀ {C : Type} {δ : C → Op C} {c b : C} {t : TimedWord},
    Skeleton δ c t b → ∀ (u : Source) (e i : Nat) (η : Nat → Nat) (x : Nat → Source),
    Ordered e i (t.map Prod.snd) η →
    ((constraint i (t.map Prod.snd)).Holds u η x ↔
      Run δ c (substitution^[e] u) (R.readout () () (retime e i (t.map Prod.snd) η)) b)

private theorem chronological_bad : ¬ chronologicalArena.Law bad := by
  intro h
  have no := (@h Unit (fun _ => .ret) () () [(0,.ret)] (Skeleton.ret rfl)
    (.of true) 0 0 (fun _ => 0) (fun _ => .of true) ⟨le_rfl,trivial⟩).mp
    (by rfl)
  cases no

def chronologicalProof : Registration chronologicalArena (type_of% (@chronological_execution)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chronological_execution, bad, chronological_bad⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, chronological_bad⟩, fun i => nomatch i⟩
  dependence := dependence

abbrev historyArena : Arena where
  signature := signature
  Law R := ∀ {C : Type} (δ : C → Op C) (c b : C) (u : Source) (x : Nat → Source),
    (∀ t : TimedWord, erase (R.readout () () t) = t) ∧
    (∀ h : Word, Run δ c u h b ↔
      ∃ (t : TimedWord) (η : Nat → Nat), Skeleton δ c t b ∧ Chronology 0 0 t η ∧
        (constraint 0 (t.map Prod.snd)).Holds u η x ∧ expand t = h ∧ erase h = t) ∧
    (∀ (D : Type) (π : TimedWord → D) (d : D),
      (∃ h : Word, Run δ c u h b ∧ π (erase h) = d) ↔
      ∃ (t : TimedWord) (η : Nat → Nat), Skeleton δ c t b ∧ Chronology 0 0 t η ∧
        (constraint 0 (t.map Prod.snd)).Holds u η x ∧ π t = d)

private theorem history_bad : ¬ historyArena.Law bad := by
  intro h
  have no := (@h Unit (fun _ => .ret) () () (.of true) (fun _ => .of true)).1 [(0,.ret)]
  cases no

def historyProof : Registration historyArena (type_of% (@native_history_correspondence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_history_correspondence, bad, history_bad⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, history_bad⟩, fun i => nomatch i⟩
  dependence := dependence

noncomputable def chronological_execution_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.chronological_execution)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.chronological_execution
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.chronologicalProof
  realizationSource := none
  generated := false
  arena := .source ⟨chronologicalArena⟩
  objectArena := .source ⟨chronologicalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chronologicalArena ⟨chronologicalProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => expand t) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","body","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def native_history_correspondence_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.native_history_correspondence)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.native_history_correspondence
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.historyProof
  realizationSource := none
  generated := false
  arena := .source ⟨historyArena⟩
  objectArena := .source ⟨historyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source historyArena ⟨historyProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => expand t) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","fn","arg","body","fn","arg","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev enumerationSignature : Signature where
  Params := EffectiveProgram × Nat × Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List (List ObserverEvent × Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def enumerationActual : Realization enumerationSignature :=
  realize enumerationSignature (fun _ p c => enumerate p.1.code p.2.1 p.2.2 c)
    (fun i => nomatch i)

def enumerationBad : Realization enumerationSignature :=
  realize enumerationSignature (fun _ _ _ => []) (fun i => nomatch i)

abbrev enumerationArena : Arena where
  signature := enumerationSignature
  Law R := ∀ (P : EffectiveProgram) (c b : Nat) (w : List ObserverEvent),
    (∃ fuel n, (w,b) ∈ R.readout () (P,fuel,n) c) ↔
    Skeleton P.transition c (untimed w) b ∧
      ∀ (u : Source) (η : Nat → Nat) (x : Nat → Source), Ordered 0 0 w η →
        ((constraint 0 w).Holds u η x ↔
          Run P.transition c u (expand (retime 0 0 w η)) b)

private def stopped : EffectiveProgram where
  code := Nat.Partrec.Code.const (Encodable.encode (Sum.inr (Sum.inr ()) : Instruction))
  step := fun _ => .inr (.inr ())
  realizes := fun c => Nat.Partrec.Code.eval_const _ c

private theorem stopped_rhs :
    Skeleton stopped.transition 0 (untimed [.ret]) 0 ∧
      ∀ (u : Source) (η : Nat → Nat) (x : Nat → Source), Ordered 0 0 [.ret] η →
        ((constraint 0 [.ret]).Holds u η x ↔
          Run stopped.transition 0 u (expand (retime 0 0 [.ret] η)) 0) := by
  refine ⟨Skeleton.ret rfl, fun u η x ho => ?_⟩
  simpa using chronological_execution
    (Skeleton.ret (δ := stopped.transition) (c := 0) (k := 0) rfl) u 0 0 η x ho

private theorem enumeration_bad : ¬ enumerationArena.Law enumerationBad := by
  intro h
  obtain ⟨fuel,n,hm⟩ := (h stopped 0 0 [.ret]).mpr stopped_rhs
  simpa [enumerationBad,realize] using hm

private theorem enumeration_dependence :
    ObservationalDependence enumerationSignature enumerationActual := by
  intro i
  obtain ⟨fuel,n,hm⟩ := (effective_native_correspondence stopped 0 0 [.ret]).mpr stopped_rhs
  refine ⟨(stopped,fuel,n),0,1,?_⟩
  change enumerate stopped.code fuel n 0 ≠ enumerate stopped.code fuel n 1
  intro he
  have hm' : ([ObserverEvent.ret],0) ∈ enumerate stopped.code fuel n 1 := by
    rw [← he]; exact hm
  have hs := ((effective_native_correspondence stopped 1 0 [.ret]).mp ⟨fuel,n,hm'⟩).1
  cases hs

def enumerationProof : Registration enumerationArena
    (type_of% (@effective_native_correspondence)) where
  actual := enumerationActual
  bridge := Iff.rfl
  variation := ⟨@effective_native_correspondence,enumerationBad,enumeration_bad⟩
  sensitivity := ⟨fun i => ⟨enumerationBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,enumeration_bad⟩,
    fun i => nomatch i⟩
  dependence := enumeration_dependence

noncomputable def effective_native_correspondence_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.effective_native_correspondence)
    (Realization enumerationSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.effective_native_correspondence
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.enumerationProof
  realizationSource := none
  generated := false
  arena := .source ⟨enumerationArena⟩
  objectArena := .source ⟨enumerationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source enumerationArena ⟨enumerationProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize enumerationSignature
    (fun _ p c => enumerate p.1.code p.2.1 p.2.2 c) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
    definition := none
    coordinates := #[0,4,5]
    readouts := #[{
      path := #["body","body","body","body","fn","arg",
        "arg","body","arg","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev burstSignature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def burstActual : Realization burstSignature :=
  realize burstSignature (fun _ k U => substitution^[k] U) (fun i => nomatch i)

def burstBad : Realization burstSignature :=
  realize burstSignature (fun _ _ _ => .of true) (fun i => nomatch i)

abbrev burstArena : Arena where
  signature := burstSignature
  Law R := ∀ {C : Type} (δ : C → Op C) (k : Nat) (c : C) (U : Source)
    (t : Word) (b : C),
    Run δ c U (List.replicate k .update ++ t) b ↔ Run δ c (R.readout () k U) t b

private def probe : Nat → Op Nat
  | 0 => .read [] (fun y => if y = .alpha then 1 else 2)
  | _ => .ret

private theorem burst_bad : ¬ burstArena.Law burstBad := by
  intro h
  have r : Run probe 0 (.of false) [.observer (.read [] .beta),.observer .ret] 2 :=
    Run.read rfl rfl (Run.ret rfl)
  have no := (@h Nat probe 0 0 (.of false) _ 2).mp r
  cases no with
  | read hop hy rest =>
    change _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.Reply.alpha = .beta at hy
    cases hy

private theorem burst_dependence : ObservationalDependence burstSignature burstActual := by
  intro i
  refine ⟨0,.of true,.of false,?_⟩
  simp [burstActual,realize]
  intro h
  cases h

def burstProof : Registration burstArena (type_of% (@updates_iff)) where
  actual := burstActual
  bridge := Iff.rfl
  variation := ⟨@updates_iff,burstBad,burst_bad⟩
  sensitivity := ⟨fun i => ⟨burstBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,burst_bad⟩,fun i => nomatch i⟩
  dependence := burst_dependence

noncomputable def updates_iff_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.updates_iff)
      (Realization burstSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.updates_iff
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.burstProof
  realizationSource := none
  generated := false
  arena := .source ⟨burstArena⟩
  objectArena := .source ⟨burstArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source burstArena ⟨burstProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize burstSignature (fun _ k U => substitution^[k] U) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
    definition := none
    coordinates := #[2]
    readouts := #[{path := #["body","body","body","body","body","body","body","arg","fn","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
