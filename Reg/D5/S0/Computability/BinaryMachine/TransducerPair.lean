import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryLanguageAudit
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.TransducerPair

set_option autoImplicit false
namespace Reg.D5.S0.Computability.BinaryMachine.TransducerPair
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Reg.Support.BinaryMachineAudit
open _root_.Complexity.TransducerPair
open _root_.Reg.Support.BinaryLanguageAudit
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace RegisterInjection

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Fin 7
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ i => simulationRegister i) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => Function.Injective (R.readout () ())

abbrev sourceScope := type_of% (@simulationRegister_injective)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Fin 7)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh : (0 : Fin 3) = 1 := h (by rfl)
  exact (by decide : (0 : Fin 3) ≠ 1) hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨simulationRegister_injective,erased,erased_fails⟩
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
    refine ⟨(),(0 : Fin 3),(1 : Fin 3),?_⟩
    change (0 : Fin 7) ≠ 2
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@simulationRegister_injective) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.TransducerPair.simulationRegister_injective.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.TransducerPair.RegisterInjection.family
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
    (fun _ _ i => simulationRegister i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.TransducerPair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RegisterInjection
namespace NormalizationBudget

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
  DependentFamily.realize signature (fun _ _ (n : Nat) => 18 * n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (M : Machine) (fuel : Nat) (input : Word) (out : Tape)
    (h : runInput M fuel input = some (true, out)) (r : Registers 6)
    (h₀ : r 0 = input) (h₂ : r 2 = []) (h₃ : r 3 = []),
    ∃ time, time ≤ R.readout () () (input.length + fuel + 2) ∧
      Exec (normalized M) (normalized M).start r time (true, StackMachine.set r 0 out.output)

abbrev sourceScope := type_of% (@Complexity.TransducerPair.exec_normalized)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨t,ht,he⟩ := h identityMachine 1 [] (Tape.ofInput []) rfl
    (fun _ => []) rfl rfl rfl
  change t ≤ 0 at ht
  have hz : t = 0 := Nat.eq_zero_of_le_zero ht
  subst t
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.TransducerPair.exec_normalized,erased,erased_fails⟩
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
    change (18 * 0 : Nat) ≠ 18 * 1
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.TransducerPair.exec_normalized) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.TransducerPair.exec_normalized.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.TransducerPair.NormalizationBudget.family
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
    (fun _ _ (n : Nat) => 18 * n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.TransducerPair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NormalizationBudget

namespace JointBudget

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
  DependentFamily.realize signature (fun _ _ (n : Nat) => 128 * n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (first second : Machine) (firstFuel secondFuel : Nat)
    (input : Word) (firstOut secondOut : Tape)
    (hfirst : runInput first firstFuel input = some (true, firstOut))
    (hsecond : runInput second secondFuel input = some (true, secondOut)),
    ∃ time, time ≤ R.readout () () (input.length + firstFuel + secondFuel + 1) ∧
      Exec (program first second) (program first second).start (StackPair.initial input) time
        (true, StackPair.initial (pairWords firstOut.output secondOut.output))

abbrev sourceScope := type_of% (@Complexity.TransducerPair.exec_program)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨t,ht,he⟩ := h identityMachine identityMachine 1 1 []
    (Tape.ofInput []) (Tape.ofInput []) rfl rfl
  change t ≤ 0 at ht
  have hz : t = 0 := Nat.eq_zero_of_le_zero ht
  subst t
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.TransducerPair.exec_program,erased,erased_fails⟩
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
    change (128 * 0 : Nat) ≠ 128 * 1
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.TransducerPair.exec_program) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.TransducerPair.exec_program.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.TransducerPair.JointBudget.family
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
    (fun _ _ (n : Nat) => 128 * n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.TransducerPair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end JointBudget

namespace PolynomialPair

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
  Law := fun R => ∀ {f g : Word → Word} (hf : PolyTime f) (hg : PolyTime g),
    R.readout () () (fun x => pairWords (f x) (g x))

abbrev sourceScope := type_of% (@Complexity.TransducerPair.polyTime_pair)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  exact h (f := fun x => x) (g := fun x => x) polyTime_id polyTime_id

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.TransducerPair.polyTime_pair,erased,erased_fails⟩
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
      (@Complexity.TransducerPair.polyTime_pair) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.TransducerPair.polyTime_pair.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.TransducerPair.PolynomialPair.family
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
    owner := `D5.S0.Computability.BinaryMachine.TransducerPair
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

end PolynomialPair

end Reg.D5.S0.Computability.BinaryMachine.TransducerPair
