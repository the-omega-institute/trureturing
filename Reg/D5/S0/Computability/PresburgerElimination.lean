import D5.S0.Computability.PresburgerElimination
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.PresburgerElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PresburgerArithmetic


namespace Audit_eval_substHead
abbrev signature : Signature where
  Params := Σ _t : Affine, Affine
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => (a.1.substHead a.2).eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (t replacement : Affine) (xs : List Int), F.readout () ⟨t,replacement⟩ xs = t.eval (replacement.eval xs :: xs)

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Affine.eval_substHead)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Affine.eval_substHead)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (.const 1) (.const 0) []
  change (0 : Int) = 1 at hh
  omega

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Affine.eval_substHead)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    refine ⟨⟨Affine.consCoeff 1 (.const 0),Affine.consCoeff 1 (.const 0)⟩,[0],[1],?_⟩
    change ((Affine.consCoeff 1 (.const 0)).substHead (Affine.consCoeff 1 (.const 0))).eval [0] ≠ ((Affine.consCoeff 1 (.const 0)).substHead (Affine.consCoeff 1 (.const 0))).eval [1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Affine.eval_substHead)
      (type_of% (realize signature (fun _ a xs => (a.1.substHead a.2).eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerElimination.Audit_eval_substHead.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerElimination.Audit_eval_substHead.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => (a.1.substHead a.2).eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerElimination,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_substHead

namespace Audit_eliminate_correct
abbrev signature : Signature where
  Params := QF
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p xs => (Cooper.eliminate p).eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : QF) (xs : List Int), F.readout () p xs = true ↔ ∃ x : Int, p.eval (x :: xs) = true

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Cooper.eliminate_correct)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Cooper.eliminate_correct)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h .truth []).mpr ⟨0,rfl⟩
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Cooper.eliminate_correct)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let p : QF := .atom (.le (Affine.consCoeff 0 (Affine.consCoeff 1 (.const 0))))
    refine ⟨p,[0],[-1],?_⟩
    change (Cooper.eliminate p).eval [0] ≠ (Cooper.eliminate p).eval [-1]
    have hz : (Cooper.eliminate p).eval [0] = true :=
      (Cooper.eliminate_correct _ _).mpr ⟨0,by simp [p,QF.eval,Atom.eval]⟩
    have ho : (Cooper.eliminate p).eval [-1] = false :=
      Bool.eq_false_of_not_eq_true (fun h => by
        obtain ⟨x,hx⟩ := (Cooper.eliminate_correct _ _).mp h
        simpa [p,QF.eval,Atom.eval] using hx)
    rw [hz,ho]
    decide


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Cooper.eliminate_correct)
      (type_of% (realize signature (fun _ p xs => (Cooper.eliminate p).eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerElimination.Audit_eliminate_correct.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerElimination.Audit_eliminate_correct.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ p xs => (Cooper.eliminate p).eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerElimination,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eliminate_correct

end Reg.D5.S0.Computability.PresburgerElimination
