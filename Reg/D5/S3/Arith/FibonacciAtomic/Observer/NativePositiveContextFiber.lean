import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout acquisitionTrace)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery (CutSet rowAt)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (HoleExterior cutExterior nameExterior)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers (labels)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation (Holds compile Record groundRecords)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber

abbrev signature : Signature where
  Params := CutSet × HoleExterior × (Address → Nat)
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p U => PositiveContext p.1 p.2.1 p.2.2 U) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (X : HoleExterior)
    (label : Address → Nat) (rep : Nat → Address)
    (well : WellAddressed P [] X)
    (representatives : ∀ n ∈ labels (nameExterior label X),
      rowAt (rep n) (nameExterior label X) = some (.of (.inr n))) (U : Source),
    R.readout () ⟨P,X,label⟩ U ↔ Holds U (compile rep [] (expression (nameExterior label X)))

private theorem seed_history :
    Holds (.of true) (compile (fun _ : Nat => []) []
      (expression (nameExterior (fun _ => 0) (.of (.inl true))))) := by
  simp [nameExterior, expression, Holds, compile, groundRecords, acquisitionTrace, Record.Holds, readout]

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact (h ∅ (.of (.inl true)) (fun _ => 0) (fun _ => [])
    (by simp [WellAddressed]) (by simp [nameExterior, labels]) (.of true)).mpr seed_history

def proof : Registration arena (type_of% (@positive_context_history_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_context_history_exact, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨∅,.of (.inl true),fun _ => 0⟩,.of true,.of false,?_⟩
    intro eq
    have present := (positive_context_history_exact ∅ (.of (.inl true))
      (fun _ => 0) (fun _ => []) (by simp [WellAddressed])
      (by simp [nameExterior, labels]) (.of true)).mpr seed_history
    have absent := eq.mp present
    have no := absent.1
    simp [cutExterior] at no
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber.positive_context_history_exact)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber.positive_context_history_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p U => PositiveContext p.1 p.2.1 p.2.2 U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber
