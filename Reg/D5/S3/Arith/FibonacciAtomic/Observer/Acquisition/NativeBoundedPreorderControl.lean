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

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
