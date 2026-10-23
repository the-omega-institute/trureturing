import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine

abbrev traceSignature : Signature where
  Params := Unit
  State _ := Trace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Trace
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ t => t) (fun e => nomatch e)

def traceBad : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => [.localStep]) (fun e => nomatch e)

abbrev deterministicArena : Arena where
  signature := traceSignature
  Law R := ∀ {C O : Type} {δ : C → Op C O} {c : C} {e : Nat} {w : List Reply}
    {t s : Trace} {b d : Boundary C O},
    Replay δ c e w t b → Replay δ c e w s d → R.readout () () t = s ∧ b = d

private theorem deterministic_bad : ¬ deterministicArena.Law traceBad := by
  intro h
  have eq := (@h Unit Unit (fun _ => .stop ()) () 0 [] [] []
    ((),0,.inr ()) ((),0,.inr ()) (Replay.stop rfl) (Replay.stop rfl)).1
  cases eq

def deterministicProof : Registration deterministicArena (type_of% (@replay_deterministic)) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@replay_deterministic,traceBad,deterministic_bad⟩
  sensitivity := ⟨fun i => ⟨traceBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,deterministic_bad⟩,fun i => nomatch i⟩
  dependence := by intro i; exact ⟨(),[],[.localStep],by simp [traceActual,realize]⟩

abbrev answersSignature : Signature where
  Params := Unit
  State _ := Trace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def answersActual : Realization answersSignature :=
  realize answersSignature (fun _ _ t => answers t) (fun e => nomatch e)

def answersBad : Realization answersSignature :=
  realize answersSignature (fun _ _ _ => [.absent]) (fun e => nomatch e)

private theorem answers_dependence : ObservationalDependence answersSignature answersActual := by
  intro i
  exact ⟨(),[],[.read 0 [] .alpha],by simp [answersActual,realize,answers,reads]⟩

abbrev operationalArena : Arena where
  signature := answersSignature
  Law R := ∀ {C O : Type} {δ : C → Op C O} {c : C} {e : Nat} {r : Source}
    {t : Trace} {o : O}, Run δ c e r t o →
    (∃ c' e', Replay δ c e (R.readout () () t) t (c',e',.inr o)) ∧
    (∀ n a y, Event.read n a y ∈ t →
      ∃ w s c', w.length < (answers t).length ∧ Replay δ c e w s (c',n,.inl a)) ∧
    (∀ w s z b d, Replay δ c e w s b → Replay δ c e w z d → s = z ∧ b = d)

private theorem operational_bad : ¬ operationalArena.Law answersBad := by
  intro h
  obtain ⟨_,_,no⟩ := (@h Unit Unit (fun _ => .stop ()) () 0 (.of true) [] () (Run.stop rfl)).1
  cases no

def operationalProof : Registration operationalArena (type_of% (@operational_replay)) where
  actual := answersActual
  bridge := Iff.rfl
  variation := ⟨@operational_replay,answersBad,operational_bad⟩
  sensitivity := ⟨fun i => ⟨answersBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,operational_bad⟩,fun i => nomatch i⟩
  dependence := answers_dependence

abbrev prefixArena : Arena where
  signature := answersSignature
  Law R := ∀ {C O : Type} {δ : C → Op C O} {c : C} {e : Nat} {r : Source}
    {t : Trace} {o : O}, Run δ c e r t o → ∀ w : List Reply, w <+: answers t →
    ∃ s b, Replay δ c e w s b ∧ s <+: t ∧ R.readout () () s = w ∧
      (w = answers t ↔ b.2.2 = .inr o)

private theorem prefix_bad : ¬ prefixArena.Law answersBad := by
  intro h
  obtain ⟨_,_,_,_,no,_⟩ := @h Unit Unit (fun _ => .stop ()) () 0 (.of true) [] ()
    (Run.stop rfl) [] (by simp [answers,reads])
  cases no

def prefixProof : Registration prefixArena (type_of% (@reached_prefix_replay)) where
  actual := answersActual
  bridge := Iff.rfl
  variation := ⟨@reached_prefix_replay,answersBad,prefix_bad⟩
  sensitivity := ⟨fun i => ⟨answersBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,prefix_bad⟩,fun i => nomatch i⟩
  dependence := answers_dependence

abbrev rootSignature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def rootActual : Realization rootSignature :=
  realize rootSignature (fun _ e u => substitution^[e] u) (fun e => nomatch e)

def rootBad : Realization rootSignature :=
  realize rootSignature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev executionArena : Arena where
  signature := rootSignature
  Law R := ∀ {C O : Type} (δ : C → Op C O) {c : C} {e : Nat} {r : Source}
    {t : Trace} {o : O}, Run δ c e r t o → ∀ u : Source, r = R.readout () e u →
    ∀ old : Trace, ∃ c' e', e ≤ e' ∧
      StateTransition.Reaches (nativeStep δ) (c,e,r,old)
        (c',e',R.readout () e' u,old ++ t) ∧ δ c' = .stop o ∧
      (∀ n a y, Event.read n a y ∈ t → readout a (R.readout () n u) = y)

private theorem execution_bad : ¬ executionArena.Law rootBad := by
  intro h
  let δ : Bool → Op Bool Unit := fun b => if b then .stop () else .applyRho true
  have run : Run δ false 0 (.of true) [.update 0] () :=
    Run.update rfl (Run.stop rfl)
  obtain ⟨c,e,_,reach,stop,_⟩ := @h Bool Unit δ false 0 (.of true) [.update 0] ()
    run (.of true) rfl []
  have actual := actual_register_execution δ run (.of true) rfl []
  obtain ⟨d,n,_,other,_,_⟩ := actual
  have comparable := StateTransition.reaches_total reach other
  -- The unique terminal physical state has beta, whereas the altered family
  -- predicts alpha at every epoch.
  have final : nativeStep δ (c,e,FreeMagma.of true,[.update 0]) = none := by
    simp [nativeStep,stop]
  have terminal : (true,1,substitution (.of true),[Event.update 0]) ∈
      StateTransition.eval (nativeStep δ) (false,0,FreeMagma.of true,[]) := by
    apply StateTransition.mem_eval.mpr
    exact ⟨Relation.ReflTransGen.single (by change nativeStep δ _ = some _; rfl),rfl⟩
  have bogus : (c,e,FreeMagma.of true,[Event.update 0]) ∈
      StateTransition.eval (nativeStep δ) (false,0,FreeMagma.of true,[]) :=
    StateTransition.mem_eval.mpr ⟨reach,final⟩
  have eq := Part.mem_unique bogus terminal
  have reg := congrArg (fun x : Config Bool => x.2.2.1) eq
  cases reg

def executionProof : Registration executionArena (type_of% (@actual_register_execution)) where
  actual := rootActual
  bridge := Iff.rfl
  variation := ⟨@actual_register_execution,rootBad,execution_bad⟩
  sensitivity := ⟨fun i => ⟨rootBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,execution_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨0,.of true,.of false,by intro eq; cases eq⟩

noncomputable def replay_deterministic_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.replay_deterministic)
    (Realization traceSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.replay_deterministic
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.deterministicProof
  realizationSource := none
  generated := false
  arena := .source ⟨deterministicArena⟩
  objectArena := .source ⟨deterministicArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deterministicArena ⟨deterministicProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def operational_replay_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.operational_replay)
    (Realization answersSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.operational_replay
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.operationalProof
  realizationSource := none
  generated := false
  arena := .source ⟨operationalArena⟩
  objectArena := .source ⟨operationalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source operationalArena ⟨operationalProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize answersSignature answersActual.readout answersActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","fn","arg","arg","body","arg","body","fn","fn","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def reached_prefix_replay_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.reached_prefix_replay)
    (Realization answersSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.reached_prefix_replay
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.prefixProof
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena⟩
  objectArena := .source ⟨prefixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena ⟨prefixProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize answersSignature answersActual.readout answersActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","fn","arg","fn","arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def actual_register_execution_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.actual_register_execution)
    (Realization rootSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.actual_register_execution
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine.executionProof
  realizationSource := none
  generated := false
  arena := .source ⟨executionArena⟩
  objectArena := .source ⟨executionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source executionArena ⟨executionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rootSignature rootActual.readout rootActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
    definition := none
    coordinates := #[4]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","domain","arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
