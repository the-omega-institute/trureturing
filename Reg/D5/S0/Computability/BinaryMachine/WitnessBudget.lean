import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.WitnessBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.WitnessBudget
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Complexity.WitnessBudget
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
namespace WitnessBudget

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
  DependentFamily.realize signature (fun _ _ (n : Nat) => n + 11) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (c e : Nat) (x w : Word),
    ∃ t out, t ≤ R.readout () () (5 * x.length + StackPower.time c e (x.length + 1) + 2 * w.length) ∧
      Exec (test c e) (test c e).start (StackPair.unpacked x w) t
        (decide (w.length ≤ powerBound c e x.length), out) ∧
      out 0 = x ∧ out 2 = List.replicate (x.length + 1) true ∧
      out 4 = [] ∧ out 5 = [] ∧ out 6 = [] ∧
      (out 3).length ≤ x.length + 3 * w.length + powerBound c e x.length + 4

abbrev sourceScope := type_of% (@Complexity.WitnessBudget.exec_test)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨t,out,ht,he,_⟩ := h 0 0 [] []
  change t ≤ 0 at ht
  have hz : t = 0 := Nat.eq_zero_of_le_zero ht
  subst t
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.WitnessBudget.exec_test,erased,erased_fails⟩
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
    change (0 + 11 : Nat) ≠ 1 + 11
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.WitnessBudget.exec_test) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.WitnessBudget.exec_test.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.WitnessBudget.WitnessBudget.family
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
    (fun _ _ (n : Nat) => n + 11) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.WitnessBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WitnessBudget

end Reg.D5.S0.Computability.BinaryMachine.WitnessBudget
