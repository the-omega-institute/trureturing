import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.StackFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.StackFrame
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

open _root_.Complexity.StackFrame
namespace FrameReadout

abbrev signature : DependentFamily.Signature where
  Params := Σ k : Nat, Σ m : Nat, Fin (k+1) → Fin (m+1)
  State := fun p => Registers p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Registers p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Σ k : Nat, Σ m : Nat, Fin (k+1) → Fin (m+1)) (r : Registers p.2.1) => _root_.Complexity.StackFrame.pull p.2.2 r) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k m : Nat} {L : Type} (i : Fin (k + 1) → Fin (m + 1))
    (hi : Function.Injective i) (p : Program k L)
    {q : L} {r out : Registers k} {t : Nat} {b : Bool}
    (h : Exec p q r t (b, out)) (big : Registers m) (hr : pull i big = r),
    ∃ result, Exec (lift i p) q big t (b, result) ∧ R.readout () ⟨k,m,i⟩ result = out ∧
      ∀ a, (∀ j, a ≠ i j) → result a = big a

abbrev sourceScope := type_of% (@Complexity.StackFrame.exec_lift)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => fun _ => ([] : List Bool)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  let r : Registers 0 := fun _ => [false]
  obtain ⟨result,_,ho,_⟩ := h (k := 0) (m := 0) (L := Unit) id
    (fun _ _ h => h) (stop 0 true) (exec_stop 0 true r) r rfl
  have hh := congrFun ho 0
  change ([] : List Bool) = [false] at hh
  cases hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackFrame.exec_lift,erased,erased_fails⟩
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
    refine ⟨(⟨0,0,id⟩ : Σ k : Nat, Σ m : Nat, Fin (k+1) → Fin (m+1)),
      (fun _ => ([] : List Bool)),(fun _ => [false]),?_⟩
    intro h
    have hh := congrFun h 0
    change ([] : List Bool) = [false] at hh
    cases hh

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackFrame.exec_lift) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackFrame.exec_lift.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackFrame.FrameReadout.family
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
    (fun _ (p : Σ k : Nat, Σ m : Nat, Fin (k+1) → Fin (m+1)) (r : Registers p.2.1) => _root_.Complexity.StackFrame.pull p.2.2 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackFrame
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FrameReadout

namespace ExtendedProgram

abbrev signature : DependentFamily.Signature where
  Params := Type
  State := fun p => Program 6 p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Program 8 p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (L : Type) (p : Program 6 L) => _root_.Complexity.StackFrame.lift _root_.Complexity.StackFrame.includeRegister p) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {L : Type} (p : Program 6 L) {q : L} {r out : Registers 6}
    {t : Nat} {b : Bool} (h : Exec p q r t (b, out)) (a saved : List Bool),
    Exec (R.readout () L p) q (extend r a saved) t (b, extend out a saved)

abbrev sourceScope := type_of% (@Complexity.StackFrame.exec_extend)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (L : Type) (p : Program 6 L) => (⟨p.start,fun _ => .halt false⟩ : Program 8 L)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  let r : Registers 6 := fun _ => []
  have he := h (stop 6 true) (exec_stop 6 true r) [] []
  have hr := he.run
  change (some (false,_) : Option (Bool × Registers 8)) = some (true,_) at hr
  cases hr

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackFrame.exec_extend,erased,erased_fails⟩
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
    refine ⟨Unit,stop 6 false,stop 6 true,?_⟩
    intro h
    have hh := congrArg (fun p : Program 8 Unit => p.code ()) h
    change (Op.halt false : Op 8 Unit) = Op.halt true at hh
    cases hh

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackFrame.exec_extend) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackFrame.exec_extend.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackFrame.ExtendedProgram.family
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
    (fun _ (L : Type) (p : Program 6 L) => _root_.Complexity.StackFrame.lift _root_.Complexity.StackFrame.includeRegister p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackFrame
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExtendedProgram

end Reg.D5.S0.Computability.BinaryMachine.StackFrame
