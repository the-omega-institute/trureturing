import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.StackCompare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.StackCompare
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Complexity.StackCompare
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
namespace CompareBudget

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ (n : Nat) => n + 3) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k : Nat} (src budget : Fin (k + 1)) (hne : src ≠ budget)
    (r : Registers k),
    ∃ t out, t ≤ R.readout () () (2 * (r src).length) ∧
      Exec (check src budget) (check src budget).start r t
        (decide ((r src).length ≤ (r budget).length), out) ∧
      ∀ a, a ≠ src → a ≠ budget → out a = r a

abbrev sourceScope := type_of% (@Complexity.StackCompare.exec_check)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨t,out,ht,he,_⟩ := h (k := 1) 0 1 (by decide) (fun _ => [])
  change t ≤ 0 at ht
  have hz : t = 0 := Nat.eq_zero_of_le_zero ht
  subst t
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackCompare.exec_check,erased,erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased,?_,rfl,erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(),(0 : Nat),(1 : Nat),?_⟩
    change (0 + 3 : Nat) ≠ 1 + 3
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackCompare.exec_check) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackCompare.exec_check.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackCompare.CompareBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ (n : Nat) => n + 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackCompare
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CompareBudget

end Reg.D5.S0.Computability.BinaryMachine.StackCompare
