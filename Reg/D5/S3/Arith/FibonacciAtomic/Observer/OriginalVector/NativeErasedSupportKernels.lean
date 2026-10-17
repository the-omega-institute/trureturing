import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
import Reg.Support.SingleDependentReadout

/-! # Dependent-family registrations for native prefix kernels -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open Observer.NativeSerialDepth (OriginalAgree)
open Observer.OriginalVector.NativeErasedSupportKernels
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The labeled prefix table is observed as its equality predicate against every second source. -/
abbrev signature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ h u => OriginalAgree h u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev twoStepArena : Arena where
  signature := signature
  Law F := ∀ (h : Nat) (u v : Source),
    (F.readout () h u v ↔
      F.readout () (h+1) (substitution^[2] u) (substitution^[2] v)) ∧
    (F.readout () h u v ↔
      ErasedAgree (h+1) (substitution^[2] u) (substitution^[2] v)) ∧
    (F.readout () h u v ↔
      SupportAgree (h+2) (substitution^[2] u) (substitution^[2] v))

abbrev evenEpochArena : Arena where
  signature := signature
  Law F := ∀ (h k : Nat), 1 ≤ k → ∀ (u v : Source),
    (ErasedAgree (h+k) (substitution^[2*k] u) (substitution^[2*k] v) ↔
      F.readout () h u v) ∧
    (SupportAgree (h+k+1) (substitution^[2*k] u) (substitution^[2*k] v) ↔
      F.readout () h u v)

theorem actual_two_step : twoStepArena.Law actual := two_step_prefix_kernel

theorem actual_even_epoch : evenEpochArena.Law actual := even_epoch_support_kernel

theorem rejected_two_step : ¬ twoStepArena.Law rejected := by
  intro h
  have no := (h 0 (.of true) (.of true)).2.1.mpr (fun _ _ => rfl)
  exact no

theorem rejected_even_epoch : ¬ evenEpochArena.Law rejected := by
  intro h
  have no := (h 0 1 (by omega) (.of true) (.of true)).1.mp (fun _ _ => rfl)
  exact no

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, (.of true), (.of false), ?_⟩
  intro he
  change OriginalAgree 0 (.of true) = OriginalAgree 0 (.of false) at he
  have no : OriginalAgree 0 (.of false) (.of true) :=
    (congrFun he (.of true)) ▸ (show OriginalAgree 0 (.of true) (.of true) from fun _ _ => rfl)
  have root := no [] (by simp)
  cases root

def twoStepFamily : Registration twoStepArena (type_of% (@two_step_prefix_kernel)) where
  actual := actual
  bridge := ⟨fun h => h, fun h => h⟩
  variation := ⟨actual_two_step, rejected, rejected_two_step⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    twoStepArena.Law actual rejected rejected_two_step
  dependence := dependence

def evenEpochFamily : Registration evenEpochArena (type_of% (@even_epoch_support_kernel)) where
  actual := actual
  bridge := ⟨fun h => h, fun h => h⟩
  variation := ⟨actual_even_epoch, rejected, rejected_even_epoch⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    evenEpochArena.Law actual rejected rejected_even_epoch
  dependence := dependence

def two_step_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@two_step_prefix_kernel) (Realization signature) Unit Unit where
  unitName := .str
    (.str `D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
      "two_step_prefix_kernel") "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
    "twoStepFamily"
  realizationSource := none
  generated := false
  arena := .source ⟨twoStepArena⟩
  objectArena := .source ⟨twoStepArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source twoStepArena ⟨twoStepFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

def even_epoch_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@even_epoch_support_kernel) (Realization signature) Unit Unit where
  unitName := .str
    (.str `D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
      "even_epoch_support_kernel") "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
    "evenEpochFamily"
  realizationSource := none
  generated := false
  arena := .source ⟨evenEpochArena⟩
  objectArena := .source ⟨evenEpochArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenEpochArena ⟨evenEpochFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms two_step_registration
#print axioms even_epoch_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativeErasedSupportKernels
