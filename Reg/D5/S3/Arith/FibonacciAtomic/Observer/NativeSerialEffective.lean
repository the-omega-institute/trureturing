import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Reply)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective

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

abbrev inclusionArena : Arena where
  signature := traceSignature
  Law R := ∀ {O : Type} (S : EffectiveService O) {c e : Nat} {r : Source}
    {t : Trace} {o : O}, ServiceRun S c e r t o →
      Run (compile S) c e r (R.readout () () t) o

private theorem inclusion_bad : ¬ inclusionArena.Law traceBad := by
  intro h
  let S : EffectiveService Unit := ⟨fun _ => (3,0,[],(0,0,0,0)),Computable.const _,0,fun _ => ()⟩
  have direct : ServiceRun S 0 0 (.of true) [] () := ServiceRun.stop (by decide) (by decide) (by decide)
  have bad := @h Unit S 0 0 (.of true) [] () direct
  cases bad with
  | localStep he _ => cases he

def inclusionProof : Registration inclusionArena (type_of% (@effective_service_inclusion)) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@effective_service_inclusion,traceBad,inclusion_bad⟩
  sensitivity := ⟨fun i => ⟨traceBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,inclusion_bad⟩,fun i => nomatch i⟩
  dependence := by intro i; exact ⟨(),[],[.localStep],by simp [traceActual,realize]⟩

noncomputable def effective_service_inclusion_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.effective_service_inclusion)
    (Realization traceSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.effective_service_inclusion
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.inclusionProof
  realizationSource := none
  generated := false
  arena := .source ⟨inclusionArena⟩
  objectArena := .source ⟨inclusionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inclusionArena ⟨inclusionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","fn","arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev originalArena : Arena where
  signature := traceSignature
  Law R := ∀ {O : Type} [Primcodable O] (S : OriginalEffectiveService O)
    {s : OriginalState} {r : Source} {t : Trace} {o : O}, OriginalRun S s r t o →
    Computable₂ (evalOriginalAction S) ∧
    ∃ nt, Run (originalNativeControl S) (originalControl s 0) s.epoch r nt o ∧
      eraseEvaluatorSteps nt = R.readout () () t ∧ reads nt = reads t ∧
      terminalObservation nt o = terminalObservation t o

private theorem erased_not_local (t : Trace) : eraseEvaluatorSteps t ≠ [.localStep] := by
  induction t with
  | nil => simp [eraseEvaluatorSteps]
  | cons e t ih => cases e <;> simp_all [eraseEvaluatorSteps]

private theorem original_bad : ¬ originalArena.Law traceBad := by
  intro law
  let S : OriginalEffectiveService Unit := {
    select := fun _ => Part.some (originalStop ())
    effective := Computable.const _ }
  have run : OriginalRun S (0, 0, 0, []) (.of true) [] () :=
    OriginalRun.stop (by simp [S])
  obtain ⟨nt,_,bad,_,_⟩ := (law S run).2
  exact erased_not_local nt bad

def originalProof : Registration originalArena (type_of% (@original_service_simulation)) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@original_service_simulation,traceBad,original_bad⟩
  sensitivity := ⟨fun i => ⟨traceBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,original_bad⟩,fun i => nomatch i⟩
  dependence := inclusionProof.dependence

noncomputable def original_service_simulation_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.original_service_simulation)
    (Realization traceSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.original_service_simulation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.originalProof
  realizationSource := none
  generated := false
  arena := .source ⟨originalArena⟩
  objectArena := .source ⟨originalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source originalArena ⟨originalProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","arg","arg","body","arg","fn","arg","arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev originalCodeArena : Arena where
  signature := traceSignature
  Law R := ∀ {O : Type} [Primcodable O] {S : OriginalEffectiveService O}
    (C : OriginalCodeRealization S)
    {s : OriginalState} {r : Source} {t : Trace} {o : O}, OriginalRun S s r t o →
    Computable₂ (evalOriginalActionCode C) ∧
    ∃ nt, Run (originalNativeControlCode C) (originalControl s 0) s.epoch r nt o ∧
      eraseEvaluatorSteps nt = R.readout () () t ∧ reads nt = reads t ∧
      terminalObservation nt o = terminalObservation t o

private theorem original_code_bad : ¬ originalCodeArena.Law traceBad := by
  intro law
  let S : OriginalEffectiveService Unit := {
    select := fun _ => Part.some (originalStop ())
    effective := Computable.const _ }
  let C : OriginalCodeRealization S := originalCodeRealization S
  have run : OriginalRun S (0, 0, 0, []) (.of true) [] () :=
    OriginalRun.stop (by simp [S])
  obtain ⟨nt,_,bad,_,_⟩ := (law C run).2
  exact erased_not_local nt bad

def originalCodeProof : Registration originalCodeArena
    (type_of% (@original_code_service_simulation)) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@original_code_service_simulation,traceBad,original_code_bad⟩
  sensitivity := ⟨fun i => ⟨traceBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,original_code_bad⟩,fun i => nomatch i⟩
  dependence := originalProof.dependence

noncomputable def original_code_service_simulation_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.original_code_service_simulation)
    (Realization traceSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.original_code_service_simulation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.originalCodeProof
  realizationSource := none
  generated := false
  arena := .source ⟨originalCodeArena⟩
  objectArena := .source ⟨originalCodeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source originalCodeArena ⟨originalCodeProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","arg","arg","body","arg","fn","arg","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev selectorSignature : Signature where
  Params := Type
  State p := OriginalAction p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := OriginalAction p
  Anchor := Empty
  finiteAnchor := inferInstance

def selectorActual : Realization selectorSignature :=
  realize selectorSignature (fun _ _ a => a) (fun e => nomatch e)

def selectorBad : Realization selectorSignature :=
  realize selectorSignature (fun _ _ _ => originalRead [] (0,0,0,0)) (fun e => nomatch e)

abbrev soundArena : Arena where
  signature := selectorSignature
  Law A := ∀ {O : Type} [Primcodable O] {S : OriginalEffectiveService O}
    (R : OriginalCodeRealization S) (s : OriginalState) {fuel : Nat} {a : OriginalAction O},
    evalOriginalActionCode R fuel (Encodable.encode s) = some a →
      A.readout () O a ∈ S.select s

private theorem sound_bad : ¬ soundArena.Law selectorBad := by
  intro law
  let S : OriginalEffectiveService Unit := {
    select := fun _ => Part.some (originalStop ())
    effective := Computable.const _ }
  let R := originalCodeRealization S
  obtain ⟨fuel,h⟩ := evalOriginalActionCode_complete R (0,0,0,[])
    (a := originalStop ()) (by simp [S])
  have bad := law R (0,0,0,[]) h
  simpa [selectorBad,realize,S,originalRead,originalStop] using bad

def soundProof : Registration soundArena (type_of% (@evalOriginalActionCode_sound)) where
  actual := selectorActual
  bridge := Iff.rfl
  variation := ⟨@evalOriginalActionCode_sound,selectorBad,sound_bad⟩
  sensitivity := ⟨fun i => ⟨selectorBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,sound_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨Unit,originalStop (),originalRead [] (0,0,0,0),by simp [selectorActual,realize,originalStop,originalRead]⟩

noncomputable def evalOriginalActionCode_sound_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.evalOriginalActionCode_sound)
    (Realization selectorSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.evalOriginalActionCode_sound
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.soundProof
  realizationSource := none
  generated := false
  arena := .source ⟨soundArena⟩
  objectArena := .source ⟨soundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source soundArena ⟨soundProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize selectorSignature selectorActual.readout selectorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev completeArena : Arena where
  signature := selectorSignature
  Law A := ∀ {O : Type} [Primcodable O] {S : OriginalEffectiveService O}
    (R : OriginalCodeRealization S) (s : OriginalState) {a : OriginalAction O},
    a ∈ S.select s → ∃ fuel,
      evalOriginalActionCode R fuel (Encodable.encode s) = some (A.readout () O a)

private theorem complete_bad : ¬ completeArena.Law selectorBad := by
  intro law
  let S : OriginalEffectiveService Unit := {
    select := fun _ => Part.some (originalStop ())
    effective := Computable.const _ }
  let R := originalCodeRealization S
  obtain ⟨fuel,h⟩ := law R (0,0,0,[]) (a := originalStop ()) (by simp [S])
  have bad := evalOriginalActionCode_sound R (0,0,0,[]) h
  simpa [selectorBad,realize,S,originalRead,originalStop] using bad

def completeProof : Registration completeArena (type_of% (@evalOriginalActionCode_complete)) where
  actual := selectorActual
  bridge := Iff.rfl
  variation := ⟨@evalOriginalActionCode_complete,selectorBad,complete_bad⟩
  sensitivity := ⟨fun i => ⟨selectorBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,complete_bad⟩,fun i => nomatch i⟩
  dependence := soundProof.dependence

noncomputable def evalOriginalActionCode_complete_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.evalOriginalActionCode_complete)
    (Realization selectorSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.evalOriginalActionCode_complete
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective.completeProof
  realizationSource := none
  generated := false
  arena := .source ⟨completeArena⟩
  objectArena := .source ⟨completeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source completeArena ⟨completeProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize selectorSignature selectorActual.readout selectorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","body","body","body","body","body","arg","body","arg","arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
