import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (literalRecord)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice

private def emptyHistory : History := ⟨[],by simp [Supported]⟩
private theorem present (side : Bool) : Stratum side emptyHistory (source side (.of true) (.of false)) :=
  (raw_stratum_iff side emptyHistory _).mpr ⟨.of true,.of false,rfl,
    by unfold Distinct F; decide +kernel,by simp [Protected,emptyHistory]⟩
private theorem absent (side : Bool) : ¬ Stratum side emptyHistory (.of true) := by
  intro h
  obtain ⟨x,y,z,h⟩ := (raw_fiber_iff _).mp h.1.1
  cases h

namespace JointChoice
abbrev signature : Signature where
  Params := Bool × History
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p u => Stratum p.1 p.2 u) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ p u => u = (if p.1 then .of false else .of true)) (fun e => nomatch e)
def witness (R : Realization signature) (H : History) (h : Nat) :=
  {p : Source × Source // R.readout () ⟨false,H⟩ p.1 ∧ R.readout () ⟨true,H⟩ p.2 ∧ Agree h p.1 p.2}
def joint (R : Realization signature) (H : History) (h : Nat) : Prop := Nonempty (witness R H h)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : OriginalHistory) (supported : Supported H),
    (∃ side : Bool, (∀ u : Source, ¬ R.readout () ⟨side,⟨H,supported⟩⟩ u) ∧
      ¬ joint R ⟨H,supported⟩ 0) ∨ (∀ h : Nat, joint R ⟨H,supported⟩ h)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  rcases h [] (by simp [Supported]) with ⟨side,no,_⟩ | all
  · exact no (if side then .of false else .of true) rfl
  · obtain ⟨p⟩ := all 0
    have left : p.val.1 = .of true := p.property.1
    have right : p.val.2 = .of false := p.property.2.1
    have no := p.property.2.2 [] (by simp)
    rw [left,right] at no
    cases no
def proof : Registration arena (type_of% (@joint_finite_choice)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@joint_finite_choice,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨false,emptyHistory⟩,source false (.of true) (.of false),.of true,?_⟩
    intro eq
    exact absent false (eq.mp (present false))

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@joint_finite_choice) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice.JointChoice.joint_finite_choice
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice.JointChoice.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => Stratum p.1 p.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","fn","arg","arg","body","fn","arg","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end JointChoice

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
