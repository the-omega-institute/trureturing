import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (acquisitionTrace frontier)
open Observer.BoundedPreorderTrial (History Report)
open Observer.Acquisition.NativeBoundedPreorderControl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution (Run)
open Observer.DelayedOriginalReadout (rightClock)
open GenealogicalFiberTransport (substitution)

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Source) (fun _ => History)

def actual : Realization signature :=
  realize signature (fun _ _ u => acquisitionTrace [] u) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : Source,
    CursorRun (some []) (R.readout () () u) none ∧
    (∀ (c : Option ActualTreeReadoutAcquisition.Address) (h : History),
      ActualCursorPrefix u c h →
      h.IsPrefix (acquisitionTrace [] u) ∧ frontier h = pending c ∧
      CursorRun (some []) h c) ∧
    (∀ (h : History) (a : Report) (s : History),
      acquisitionTrace [] u = h ++ a :: s →
      CursorRun (some []) h (some a.1) ∧
      frontier h = a.1 :: rightsPending a.1 ∧
      CursorRun (cursorStep a.1 a.2) s none)

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have impossible := (law (.of true)).1
  change CursorRun (some []) [] none at impossible
  cases impossible

def family : Registration arena
    (type_of% (@reachable_compressed_frontier_and_trial_simulation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reachable_compressed_frontier_and_trial_simulation, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_law
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    change acquisitionTrace [] (.of true) ≠ acquisitionTrace [] (.of false)
    simp [acquisitionTrace]

def reachable_compressed_frontier_and_trial_simulation_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@reachable_compressed_frontier_and_trial_simulation)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev alignmentSignature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Source) (fun _ => Nat)

def alignmentActual : Realization alignmentSignature :=
  realize alignmentSignature (fun _ _ u => rightClock u) (fun e => nomatch e)

def alignmentBad : Realization alignmentSignature :=
  realize alignmentSignature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev alignmentArena : Arena where
  signature := alignmentSignature
  Law R := ∀ (h T t : Nat) (u : Source), u.length = h → t ≤ T →
    let B := alignmentBudget h T
    let U := B - t - R.readout () () u
    0 < U ∧ t + U = B - rightClock u ∧
    B - 2 * h + 1 ≤ t + U ∧ t + U ≤ B ∧
    t + U - (B - 2 * h + 1) ≤ 2 * h - 1 ∧
    Run (controlProgram (activeParameters h T))
      (Observer.NativePollingAlignment.observations (substitution^[t] u))
      (canonical .poll) 0 (fresh 0) U

private theorem alignment_bad_law : ¬ alignmentArena.Law alignmentBad := by
  intro law
  have impossible := law 1 0 0 (.of true) rfl (by decide)
  change 0 < 0 ∧ _ at impossible
  exact Nat.lt_irrefl 0 impossible.1

def alignmentFamily : Registration alignmentArena (type_of% (@native_one_update_alignment)) where
  actual := alignmentActual
  bridge := Iff.rfl
  variation := ⟨@native_one_update_alignment, alignmentBad, alignment_bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ alignment_bad_law
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    change (0 : Nat) ≠ 1
    decide

def native_one_update_alignment_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@native_one_update_alignment) (Realization alignmentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl.alignmentUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl.alignmentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨alignmentArena⟩
  objectArena := .source ⟨alignmentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source alignmentArena ⟨alignmentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize alignmentSignature alignmentActual.readout alignmentActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
