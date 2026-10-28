import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryLanguageAudit
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.PairProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.PairProjection
open _root_.Complexity.PairProjection
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Reg.Support.BinaryMachineAudit
open _root_.Reg.Support.BinaryLanguageAudit
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace PolynomialProjection

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Word → Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ (n : Word → Word) => Complexity.PolyTime n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (right : Bool) (fallback : Word),
    R.readout () () (project right fallback)

abbrev sourceScope := type_of% (@Complexity.PairProjection.polyTime_project)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  exact h false []

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.PairProjection.polyTime_project,erased,erased_fails⟩
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
    refine ⟨(),(fun x : Word => x),diagonalOutput,?_⟩
    change PolyTime (fun x => x) ≠ PolyTime diagonalOutput
    intro heq
    exact diagonal_not_polyTime (heq ▸ polyTime_id)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.PairProjection.polyTime_project) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.PairProjection.polyTime_project.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.PairProjection.PolynomialProjection.family
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
    (fun _ _ (n : Word → Word) => Complexity.PolyTime n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.PairProjection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialProjection

end Reg.D5.S0.Computability.BinaryMachine.PairProjection
