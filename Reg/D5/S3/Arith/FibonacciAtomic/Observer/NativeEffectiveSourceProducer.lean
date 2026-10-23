import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective (OriginalEvent)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer

abbrev signature : Signature where
  Params := Σ _ : Nat, List OriginalEvent
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => sourceName U) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i : Nat) (H : List OriginalEvent) (U : Source),
    FullSourceAcquisition (R.readout () ⟨i,H⟩ U) U i H

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb : sourceDecoder 0 = some (.of false) := (h 0 [] (.of false)).2.2.1
  have hg : sourceDecoder 0 = some (.of true) :=
    (effective_source_producer 0 [] (.of true)).2.2.1
  have eq := Option.some.inj (hg.symm.trans hb)
  cases eq

def proof : Registration arena (type_of% (@effective_source_producer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@effective_source_producer,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨⟨0,[]⟩,.of true,.of false,by simp [actual,realize,sourceName]⟩

noncomputable def effective_source_producer_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer.effective_source_producer)
      (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer.effective_source_producer
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","fn","fn","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer
