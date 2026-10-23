import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (acquisitionTrace frontier)
open Observer.BoundedPreorderTrial (History Report)
open Observer.Acquisition.NativeBoundedPreorderRows
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
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
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
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.alignmentUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.alignmentFamily
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
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

abbrev stationarySignature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Source) (fun _ => Bool)

def stationaryActual : Realization stationarySignature :=
  realize stationarySignature
    (fun _ _ u => decide ((GenealogicalFiberTransport.composition u).2 % 2 = 1))
    (fun e => nomatch e)

def stationaryBad : Realization stationarySignature :=
  realize stationarySignature (fun _ _ _ => true) (fun e => nomatch e)

abbrev stationaryArena : Arena where
  signature := stationarySignature
  Law R := ∀ (P : Parameters) (τ : Nat) (u y : Source),
    u.length = P.h → y = substitution^[τ] u → P.start ≤ τ → τ ≤ P.start + P.last →
    (P.h % 2 = 0 ∨ τ = 0) →
    ∀ (obs : Nat → ActualTreeReadoutAcquisition.Address → ActualTreeReadoutAcquisition.Reply)
      (epoch : Nat),
    (∀ p, obs epoch p = ActualTreeReadoutAcquisition.readout p y) →
    let bit := R.readout () () u
    let final := canonical (if bit then .halt1 else .halt0)
    Run (controlProgram P) obs (fresh 0) epoch final epoch ∧
    controlProgram P final = .halt ∧
    (∀ z a, Run (controlProgram P) obs (fresh 0) epoch z a →
      controlProgram P z = .halt → z = final ∧ a = epoch) ∧
    (∀ z a, Run (controlProgram P) obs (fresh 0) epoch z a →
      a = epoch ∧ (z = final ∨ TrialPoint P τ u z))

private theorem stationary_bad_law : ¬ stationaryArena.Law stationaryBad := by
  intro law
  let P : Parameters := ⟨1, 0, 0, 0, false⟩
  let obs : Nat → ActualTreeReadoutAcquisition.Address → ActualTreeReadoutAcquisition.Reply :=
    fun _ p => ActualTreeReadoutAcquisition.readout p (.of true)
  have wrong := law P 0 (.of true) (.of true) rfl rfl (by decide) (by decide)
    (Or.inr rfl) obs 0 (by intro p; rfl)
  have correct := native_stationary_bounded_execution P 0 (.of true) (.of true) rfl rfl
    (by decide) (by decide) (Or.inr rfl) obs 0 (by intro p; rfl)
  have eq := correct.2.2.1 _ _ wrong.1 wrong.2.1
  have mode := congrArg Control.mu eq.1
  change Mode.halt1 = Mode.halt0 at mode
  cases mode

def stationaryFamily : Registration stationaryArena
    (type_of% (@native_stationary_bounded_execution)) where
  actual := stationaryActual
  bridge := Iff.rfl
  variation := ⟨@native_stationary_bounded_execution, stationaryBad, stationary_bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ stationary_bad_law
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    change (false : Bool) ≠ true
    decide

def native_stationary_bounded_execution_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@native_stationary_bounded_execution) (Realization stationarySignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.stationaryUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.stationaryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stationaryArena⟩
  objectArena := .source ⟨stationaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stationaryArena ⟨stationaryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stationarySignature stationaryActual.readout stationaryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev rowsArena : Arena where
  signature := stationarySignature
  Law R := ∀ (h T t : Nat) (u : Source),
    u.length = h → t ≤ T → (T = 0 ∨ h % 2 = 0) → ∀ active : Bool,
    let P := rowParameters h T active
    let U := rowUpdates h T t u active
    let bit := R.readout () () u
    let final := canonical (if bit then .halt1 else .halt0)
    P.start ≤ t + U ∧ t + U ≤ P.start + P.last ∧
    (U = 0 ∨ (0 < U ∧ t + U = alignmentBudget h T - rightClock u)) ∧
    Run (controlProgram P) (Observer.NativePollingAlignment.observations (substitution^[t] u))
      (rowInitial T active) 0 final U ∧
    controlProgram P final = .halt ∧
    (∀ z a, Run (controlProgram P) (Observer.NativePollingAlignment.observations (substitution^[t] u))
      (rowInitial T active) 0 z a → controlProgram P z = .halt → z = final ∧ a = U) ∧
    (∀ z a, Run (controlProgram P) (Observer.NativePollingAlignment.observations (substitution^[t] u))
      (rowInitial T active) 0 z a → RowPoint P (t + U) u U z a)

private theorem rows_bad_law : ¬ rowsArena.Law stationaryBad := by
  intro law
  have wrong := law 1 0 0 (.of true) rfl (by decide) (Or.inl rfl) false
  obtain ⟨_, _, _, _, _, unique, _⟩ :=
    native_bounded_rows_execution 1 0 0 (.of true) rfl (by decide) (Or.inl rfl) false
  have eq := unique _ _ wrong.2.2.2.1 wrong.2.2.2.2.1
  have mode := congrArg Control.mu eq.1
  change Mode.halt1 = Mode.halt0 at mode
  cases mode

def rowsFamily : Registration rowsArena (type_of% (@native_bounded_rows_execution)) where
  actual := stationaryActual
  bridge := Iff.rfl
  variation := ⟨@native_bounded_rows_execution, stationaryBad, rows_bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rows_bad_law
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    change (false : Bool) ≠ true
    decide

def native_bounded_rows_execution_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@native_bounded_rows_execution) (Realization stationarySignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.rowsUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows.rowsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rowsArena⟩
  objectArena := .source ⟨rowsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowsArena ⟨rowsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stationarySignature stationaryActual.readout stationaryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
