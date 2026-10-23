import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (acquisitionTrace nodes)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => U) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : Source,
    Run sourceControl initialControl 0 U (productionTrace [] U) (R.readout () () U) ∧
    (∀ old : Trace, ∃ c : Control,
      StateTransition.Reaches (nativeStep sourceControl) (initialControl,0,U,old)
        (c,0,U,old ++ productionTrace [] U) ∧ sourceControl c = .stop U) ∧
    (∀ (old : Trace) (x : Config Control),
      StateTransition.Reaches (nativeStep sourceControl) (initialControl,0,U,old) x →
        x.2.1 = 0 ∧ x.2.2.1 = U) ∧
    reads (productionTrace [] U) =
      (acquisitionTrace [] U).map (fun a => (0,a.1,a.2)) ∧
    (reads (productionTrace [] U)).map (fun a => a.2.1) = nodes U ∧
    ((reads (productionTrace [] U)).map (fun a => a.2.1)).Nodup ∧
    (reads (productionTrace [] U)).length = (nodes U).length

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have run := (h (.of false)).1
  change Run sourceControl (.visit [] []) 0 (.of false) [.read 0 [] .beta] (.of true) at run
  cases run with
  | read query reply next =>
      simp only [sourceControl, Op.read.injEq] at query
      rcases query with ⟨_,hk⟩
      rw [← hk] at next
      cases next with
      | stop eq => cases eq

def proof : Registration arena (type_of% (@native_source_producer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_source_producer,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(),.of true,.of false,by intro eq; cases eq⟩

noncomputable def native_source_producer_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer.native_source_producer)
    (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer.native_source_producer
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer
