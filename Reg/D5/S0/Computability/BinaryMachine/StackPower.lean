import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryLanguageAudit
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.StackPower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.StackPower
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Complexity.StackPower
open _root_.Reg.Support.BinaryMachineAudit
open _root_.Reg.Support.BinaryLanguageAudit
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
namespace MultiplyBudget

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
  DependentFamily.realize signature (fun _ _ (n : Nat) => n + 8) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (r : Registers 6) (count n : Nat)
    (hc : r 3 = List.replicate count true) (hb : r 2 = List.replicate n true)
    (h₄ : r 4 = []) (h₅ : r 5 = []) (h₆ : r 6 = []),
    Exec multiply multiply.start r (R.readout () () (count * (11 * n + 9)))
      (true, StackMachine.set r 3 (List.replicate (count * n) true))

abbrev sourceScope := type_of% (@Complexity.StackPower.exec_multiply)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h (fun _ => []) 0 0 rfl rfl rfl rfl rfl
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackPower.exec_multiply,erased,erased_fails⟩
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
    change (0 + 8 : Nat) ≠ 1 + 8
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackPower.exec_multiply) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackPower.exec_multiply.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackPower.MultiplyBudget.family
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
    (fun _ _ (n : Nat) => n + 8) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackPower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MultiplyBudget

namespace NumericalEnvelope

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Nat → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ (n : Nat → Nat) => Complexity.PolynomialBound n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (c e : Nat),
    R.readout () () (time c e)

abbrev sourceScope := type_of% (@Complexity.StackPower.polynomialBound_time)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  exact h 0 0

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackPower.polynomialBound_time,erased,erased_fails⟩
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
    refine ⟨(),(fun _ : Nat => 0),diagonalSize,?_⟩
    change PolynomialBound (fun _ => 0) ≠ PolynomialBound diagonalSize
    intro heq
    exact diagonal_not_bounded (heq ▸ PolynomialBound.constant 0)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackPower.polynomialBound_time) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackPower.polynomialBound_time.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackPower.NumericalEnvelope.family
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
    (fun _ _ (n : Nat → Nat) => Complexity.PolynomialBound n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackPower
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

end NumericalEnvelope

namespace PowerCount

abbrev signature : DependentFamily.Signature where
  Params := Σ _ : Nat, Nat
  State := fun p => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Σ _ : Nat, Nat) (n : Nat) => _root_.Complexity.StackPower.time p.1 p.2 n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (c e n : Nat) (r : Registers 6)
    (hb : r 2 = List.replicate n true) (h₃ : r 3 = [])
    (h₄ : r 4 = []) (h₅ : r 5 = []) (h₆ : r 6 = []),
    Exec (power c e) (power c e).start r (R.readout () ⟨c,e⟩ n)
      (true, StackMachine.set r 3 (List.replicate (c * n ^ e) true))

abbrev sourceScope := type_of% (@Complexity.StackPower.exec_power)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h 0 0 0 (fun _ => []) rfl rfl rfl rfl rfl
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackPower.exec_power,erased,erased_fails⟩
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
    refine ⟨(⟨1,1⟩ : Σ _ : Nat, Nat),(0 : Nat),(1 : Nat),?_⟩
    change _root_.Complexity.StackPower.time 1 1 0 ≠ _root_.Complexity.StackPower.time 1 1 1
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackPower.exec_power) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackPower.exec_power.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackPower.PowerCount.family
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
    (fun _ (p : Σ _ : Nat, Nat) (n : Nat) => _root_.Complexity.StackPower.time p.1 p.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackPower
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PowerCount

end Reg.D5.S0.Computability.BinaryMachine.StackPower
