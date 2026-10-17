import Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
import Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
open Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness

def captureBad : Realization frontierSignature :=
  realize frontierSignature (fun _ _ _ => ⟨.ready true rootBytes,.of true,false⟩)
    (fun i => nomatch i)

abbrev captureArena : Arena where
  signature := frontierSignature
  Law R := ∀ (u : Source) (σ : Nat → Bool) (n : Nat) (q : Bool) (row : List Cell),
    (R.readout () (u,σ) n).config = .ready q row → Captured u σ n q row

private theorem capture_bad : ¬ captureArena.Law captureBad := by
  intro h
  obtain ⟨v,w,lower,_⟩ := h (.of true) (fun _ => false) 0 true rootBytes rfl
  omega

def captureProof : Registration captureArena (type_of% (@returning_capture)) where
  actual := frontierActual
  bridge := Iff.rfl
  variation := ⟨@returning_capture,captureBad,capture_bad⟩
  sensitivity := ⟨fun i => ⟨captureBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,capture_bad⟩,fun i => nomatch i⟩
  dependence := frontier_dependence

noncomputable def returning_capture_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness.returning_capture)
      (Realization frontierSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness.returning_capture
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness.captureProof
  realizationSource := none
  generated := false
  arena := .source ⟨captureArena⟩
  objectArena := .source ⟨captureArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source captureArena ⟨captureProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize frontierSignature
    (fun _ p n => trajectory p.2 ⟨.entry,p.1,false⟩ n) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","domain","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def rawBad : Realization supportSignature :=
  realize supportSignature (fun _ _ c => match c with
    | .entry => .localStep (.ready true []) | _ => .ret) (fun i => nomatch i)

abbrev rawArena : Arena where
  signature := supportSignature
  Law R := ∀ (u : Source) (h : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.Word)
    (q : Bool) (row : List Cell),
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.Run
      (R.readout () ()) .entry u h (.ready q row) → Captured u (eventSchedule h) h.length q row

private theorem raw_bad : ¬ rawArena.Law rawBad := by
  intro h
  have run : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution.Run
      (rawBad.readout () ()) .entry (.of true)
      [.observer .localStep,.observer .ret] (.ready true []) :=
    .localStep rfl (.ret rfl)
  obtain ⟨v,w,_,_,_,_,_,_,_,bytes,_,_⟩ := h (.of true) _ true [] run
  simp [recordBytes,rootBytes] at bytes

def rawProof : Registration rawArena (type_of% (@all_returning_histories)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@all_returning_histories,rawBad,raw_bad⟩
  sensitivity := ⟨fun i => ⟨rawBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,raw_bad⟩,fun i => nomatch i⟩
  dependence := pair_completeProof.dependence

noncomputable def all_returning_histories_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness.all_returning_histories)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness.all_returning_histories
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness.rawProof
  realizationSource := none
  generated := false
  arena := .source ⟨rawArena⟩
  objectArena := .source ⟨rawArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rawArena ⟨rawProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","domain","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness
