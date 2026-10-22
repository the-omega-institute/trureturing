import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound
import Reg.Support.DependentFamily

/-! Audit registration for the native future-memory lower bound. -/

set_option autoImplicit false
noncomputable section

universe u

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Reply)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeJointFutureClasses
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Reply × Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ u => futureReplies u) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => fun _ => (.absent, .absent)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {W : Type u} [Fintype W]
    (memory : Source → W)
    (memory_surjective : Function.Surjective memory)
    (memoryReadout : W → ℕ → Reply × Reply),
    (∀ u k, R.readout () () u k = memoryReadout (memory u) k) →
      11 ≤ Fintype.card W

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let memory : Source → ULift.{u} (Fin 1) := fun _ => ⟨0⟩
  let memoryReadout : ULift.{u} (Fin 1) → ℕ → Reply × Reply :=
    fun _ _ => (.absent, .absent)
  have memory_surjective : Function.Surjective memory := by
    intro w
    exact ⟨.of false, Subsingleton.elim _ _⟩
  have future_factor : ∀ u k,
      rejected.readout () () u k = memoryReadout (memory u) k := by
    intro u k
    rfl
  have hcard := h (W := ULift.{u} (Fin 1))
    (memory := memory) (memory_surjective := memory_surjective)
    (memoryReadout := memoryReadout) future_factor
  norm_num [memory, rejected, realize, memoryReadout] at hcard

def family : Registration arena.{u}
    (type_of% (@native_joint_future_memory_lower_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_joint_future_memory_lower_bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro h
    have he := congrFun h 1
    change futureReplies (.of true) 1 = futureReplies (.of false) 1 at he
    have hn : futureReplies (.of true) 1 ≠ futureReplies (.of false) 1 := by decide
    exact hn he

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound.native_joint_future_memory_lower_bound.{u})
    (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => futureReplies u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound
