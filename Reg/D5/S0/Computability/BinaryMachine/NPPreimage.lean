import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryLanguageAudit
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.NPPreimage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.NPPreimage
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Reg.Support.BinaryMachineAudit
open _root_.Reg.Support.BinaryLanguageAudit
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace VerifierClass

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Language
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ (n : Language) => Complexity.InNP n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {A : Language} {f : Word → Word}
    (hA : InNP A) (hf : PolyTime f),
    R.readout () () (fun x => A (f x))

abbrev sourceScope := type_of% (@Complexity.inNP_preimage)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  exact h (A := fun _ => True) (f := fun x => x) full_inNP polyTime_id

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.inNP_preimage,erased,erased_fails⟩
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
    refine ⟨(),(fun _ : Word => True),diagonalLanguage,?_⟩
    change InNP (fun _ => True) ≠ InNP diagonalLanguage
    intro heq
    exact diagonal_not_inNP (heq ▸ full_inNP)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.inNP_preimage) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.inNP_preimage.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.NPPreimage.VerifierClass.family
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
    (fun _ _ (n : Language) => Complexity.InNP n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.NPPreimage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end VerifierClass

end Reg.D5.S0.Computability.BinaryMachine.NPPreimage
