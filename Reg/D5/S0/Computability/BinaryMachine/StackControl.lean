import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryMachineAudit
import D5.S0.Computability.BinaryMachine.StackControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.BinaryMachine.StackControl
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.Complexity.StackMachine (Registers)
open _root_.Complexity.StackControl
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
namespace LiteralBudget

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
  DependentFamily.realize signature (fun _ _ (n : Nat) => n + 1) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k : Nat} (j : Fin (k + 1)) (xs : List Bool) (r : Registers k),
    Exec (write j xs) (write j xs).start r (R.readout () () (2 * xs.length))
      (true, StackMachine.set r j (xs ++ r j))

abbrev sourceScope := type_of% (@Complexity.StackControl.exec_write)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h (k := 0) 0 [] (fun _ => [])
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackControl.exec_write,erased,erased_fails⟩
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
    change (0 + 1 : Nat) ≠ 1 + 1
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackControl.exec_write) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackControl.exec_write.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackControl.LiteralBudget.family
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
    (fun _ _ (n : Nat) => n + 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LiteralBudget

namespace MoveBudget

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
  DependentFamily.realize signature (fun _ _ (n : Nat) => n + 6) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []),
    Exec (moveWord src dst scratch) (moveWord src dst scratch).start r
      (R.readout () () ((r dst).length + 4 * (r src).length))
      (true, StackMachine.set (StackMachine.set r src []) dst (r src))

abbrev sourceScope := type_of% (@Complexity.StackControl.exec_moveWord)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h (k := 2) 0 1 2 (by decide) (by decide) (by decide) (fun _ => []) rfl
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackControl.exec_moveWord,erased,erased_fails⟩
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
    change (0 + 6 : Nat) ≠ 1 + 6
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackControl.exec_moveWord) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackControl.exec_moveWord.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackControl.MoveBudget.family
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
    (fun _ _ (n : Nat) => n + 6) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MoveBudget

namespace ChoiceCount

abbrev signature : DependentFamily.Signature where
  Params := Nat
  State := fun p => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Nat) (s : Nat) => p + s) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k : Nat} {A B : Type} (p : Program k A) (yes no : Program k B)
    {q : A} {r middle out : Registers k} {t s : Nat} {b d : Bool}
    (hp : Exec p q r t (b, middle))
    (hq : Exec (if b then yes else no) (if b then yes else no).start middle s (d, out)),
    Exec (choose p yes no) (.inl q) r (R.readout () t s) (d, out)

abbrev sourceScope := type_of% (@Complexity.StackControl.exec_choose)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  let r : Registers 0 := fun _ => []
  have he := h (stop 0 true) (stop 0 true) (stop 0 true)
    (exec_stop 0 true r) (exec_stop 0 true r)
  exact no_zero_exec he

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackControl.exec_choose,erased,erased_fails⟩
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
    refine ⟨(0 : Nat),(0 : Nat),(1 : Nat),?_⟩
    change (0 + 0 : Nat) ≠ 0 + 1
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackControl.exec_choose) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackControl.exec_choose.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackControl.ChoiceCount.family
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
    (fun _ (p : Nat) (s : Nat) => p + s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackControl
    definition := none
    coordinates := #[10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChoiceCount

namespace WidenLeftProgram

abbrev signature : DependentFamily.Signature where
  Params := Σ _ : Nat, Σ _ : Type, Type
  State := fun p => Program p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Program p.1 (Sum p.2.1 p.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Σ _ : Nat, Σ _ : Type, Type) (q : Program p.1 p.2.1) => _root_.Complexity.StackControl.widenLeft (B := p.2.2) q) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k : Nat} {A B : Type} (p : Program k A)
    {r out : Registers k} {t : Nat} {b : Bool}
    (h : Exec p p.start r t (b, out)),
    Exec (R.readout () ⟨k,A,B⟩ p) (widenLeft p).start r t (b, out)

abbrev sourceScope := type_of% (@Complexity.StackControl.exec_widenLeft)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Σ _ : Nat, Σ _ : Type, Type) (q : Program p.1 p.2.1) => (⟨.inl q.start,fun _ => .halt false⟩ : Program p.1 (Sum p.2.1 p.2.2))) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  let r : Registers 0 := fun _ => []
  have he := h (k := 0) (A := Unit) (B := Unit) (stop 0 true) (exec_stop 0 true r)
  have hr := he.run
  change (some (false,_) : Option (Bool × Registers 0)) = some (true,_) at hr
  cases hr

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackControl.exec_widenLeft,erased,erased_fails⟩
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
    refine ⟨(⟨0,Unit,Unit⟩ : Σ _ : Nat, Σ _ : Type, Type),stop 0 false,stop 0 true,?_⟩
    intro h
    have hh := congrArg (fun p : Program 0 (Sum Unit Unit) => p.code (.inl ())) h
    change (Op.halt false : Op 0 (Sum Unit Unit)) = Op.halt true at hh
    cases hh

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackControl.exec_widenLeft) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackControl.exec_widenLeft.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackControl.WidenLeftProgram.family
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
    (fun _ (p : Σ _ : Nat, Σ _ : Type, Type) (q : Program p.1 p.2.1) => _root_.Complexity.StackControl.widenLeft (B := p.2.2) q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackControl
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WidenLeftProgram

namespace WidenRightProgram

abbrev signature : DependentFamily.Signature where
  Params := Σ _ : Nat, Σ _ : Type, Type
  State := fun p => Program p.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Program p.1 (Sum p.2.1 p.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Σ _ : Nat, Σ _ : Type, Type) (q : Program p.1 p.2.2) => _root_.Complexity.StackControl.widenRight (A := p.2.1) q) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ {k : Nat} {A B : Type} (p : Program k B)
    {r out : Registers k} {t : Nat} {b : Bool}
    (h : Exec p p.start r t (b, out)),
    Exec (R.readout () ⟨k,A,B⟩ p) (widenRight p).start r t (b, out)

abbrev sourceScope := type_of% (@Complexity.StackControl.exec_widenRight)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ (p : Σ _ : Nat, Σ _ : Type, Type) (q : Program p.1 p.2.2) => (⟨.inr q.start,fun _ => .halt false⟩ : Program p.1 (Sum p.2.1 p.2.2))) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  let r : Registers 0 := fun _ => []
  have he := h (k := 0) (A := Unit) (B := Unit) (stop 0 true) (exec_stop 0 true r)
  have hr := he.run
  change (some (false,_) : Option (Bool × Registers 0)) = some (true,_) at hr
  cases hr

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨Complexity.StackControl.exec_widenRight,erased,erased_fails⟩
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
    refine ⟨(⟨0,Unit,Unit⟩ : Σ _ : Nat, Σ _ : Type, Type),stop 0 false,stop 0 true,?_⟩
    intro h
    have hh := congrArg (fun p : Program 0 (Sum Unit Unit) => p.code (.inr ())) h
    change (Op.halt false : Op 0 (Sum Unit Unit)) = Op.halt true at hh
    cases hh

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@Complexity.StackControl.exec_widenRight) (DependentFamily.Realization signature) Unit Unit where
  unitName := `Complexity.StackControl.exec_widenRight.__information_unit
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.StackControl.WidenRightProgram.family
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
    (fun _ (p : Σ _ : Nat, Σ _ : Type, Type) (q : Program p.1 p.2.2) => _root_.Complexity.StackControl.widenRight (A := p.2.1) q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.StackControl
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WidenRightProgram

end Reg.D5.S0.Computability.BinaryMachine.StackControl
