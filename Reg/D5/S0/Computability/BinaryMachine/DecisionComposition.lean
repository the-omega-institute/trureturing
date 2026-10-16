import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryLanguageAudit
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.DecisionComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.DecisionComposition
open _root_.Complexity.DecisionComposition
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Reg.Support.BinaryMachineAudit
open _root_.Reg.Support.BinaryLanguageAudit
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace PolynomialDecision

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Machine
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ (n : Machine) => Complexity.PolynomialTimeMachine n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {f : Word → Word} (hf : PolyTime f) (M : Machine)
    (hM : PolynomialTimeMachine M),
    ∃ N : Machine, R.readout () () N ∧ ∀ x, Accepts N x ↔ Accepts M (f x)

abbrev sourceScope := type_of% (@Complexity.DecisionComposition.preprocess)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨N,hn,_⟩ := h (f := fun x => x) polyTime_id identityMachine identity_polynomial
  exact hn

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.DecisionComposition.preprocess,erased,erased_fails⟩
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
    refine ⟨(),identityMachine,spinning,?_⟩
    change PolynomialTimeMachine identityMachine ≠ PolynomialTimeMachine spinning
    intro heq
    exact spinning_not_polynomial (heq ▸ identity_polynomial)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.DecisionComposition.preprocess) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.DecisionComposition.preprocess.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.DecisionComposition.PolynomialDecision.family
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
    (fun _ _ (n : Machine) => Complexity.PolynomialTimeMachine n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.DecisionComposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialDecision

end Reg.D5.S0.Computability.BinaryMachine.DecisionComposition
