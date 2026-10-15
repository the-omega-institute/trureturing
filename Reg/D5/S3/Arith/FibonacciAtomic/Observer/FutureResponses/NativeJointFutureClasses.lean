import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureClasses
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureClasses

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Reply)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeJointFutureClasses
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
  (fun _ _ _ _ => (.branch, .branch)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (∀ u v : Source,
    (∀ k : ℕ, R.readout () () u k = R.readout () () v k) ↔ jointClass u = jointClass v) ∧
    Function.Surjective jointClass ∧ Fintype.card JointClass = 11

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h.1 (.of true) (.of false)).mp (fun _ => rfl)
  cases he

def family : Registration arena (type_of% (@native_joint_future_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_joint_future_classification, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeJointFutureClasses.native_joint_future_classification)
    (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureClasses.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureClasses.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
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

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureClasses
