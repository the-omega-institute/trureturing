import D5.S0.Computability.PresburgerDecision
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.PresburgerDecision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PresburgerArithmetic


namespace Audit_holds_iff_quantifierEliminate
abbrev signature : Signature where
  Params := Formula
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p xs => p.quantifierEliminate.eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : Formula) (xs : List Int), p.holds xs ↔ F.readout () p xs = true

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Formula.holds_iff_quantifierEliminate)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Formula.holds_iff_quantifierEliminate)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (.qf .truth) []).mp rfl
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Formula.holds_iff_quantifierEliminate)) where
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
    refine ⟨Formula.qf (.atom (.le (Affine.consCoeff 1 (.const 0)))),[0],[-1],?_⟩
    dsimp only [actual, realize]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Formula.holds_iff_quantifierEliminate)
      (type_of% (realize signature (fun _ p xs => p.quantifierEliminate.eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerDecision.Audit_holds_iff_quantifierEliminate.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerDecision.Audit_holds_iff_quantifierEliminate.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ p xs => p.quantifierEliminate.eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerDecision,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_holds_iff_quantifierEliminate

namespace Audit_decideHolds_eq_true_iff
abbrev signature : Signature where
  Params := Formula
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p xs => p.decideHolds xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : Formula) (xs : List Int), F.readout () p xs = true ↔ p.holds xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Formula.decideHolds_eq_true_iff)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Formula.decideHolds_eq_true_iff)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (.qf .truth) []).mpr rfl
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Formula.decideHolds_eq_true_iff)) where
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
    refine ⟨Formula.qf (.atom (.le (Affine.consCoeff 1 (.const 0)))),[0],[-1],?_⟩
    change (Formula.qf (.atom (.le (Affine.consCoeff 1 (.const 0))))).decideHolds [0] ≠ (Formula.qf (.atom (.le (Affine.consCoeff 1 (.const 0))))).decideHolds [-1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Formula.decideHolds_eq_true_iff)
      (type_of% (realize signature (fun _ p xs => p.decideHolds xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerDecision.Audit_decideHolds_eq_true_iff.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerDecision.Audit_decideHolds_eq_true_iff.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ p xs => p.decideHolds xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerDecision,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_decideHolds_eq_true_iff

namespace Audit_decideSentence_eq_true_iff
abbrev signature : Signature where
  Params := Unit
  State a := Formula
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ p => Formula.decideSentence p) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : Formula.Sentence), F.readout () () p = true ↔ p.holds []

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Formula.decideSentence_eq_true_iff)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Formula.decideSentence_eq_true_iff)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (.qf .truth)).mpr rfl
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Formula.decideSentence_eq_true_iff)) where
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
    refine ⟨(),Formula.qf .truth, Formula.qf .falsity,?_⟩
    change Formula.decideSentence (.qf .truth) ≠ Formula.decideSentence (.qf .falsity)
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Formula.decideSentence_eq_true_iff)
      (type_of% (realize signature (fun _ _ p => Formula.decideSentence p) (fun e => nomatch e)))
      (type_of% (Formula)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerDecision.Audit_decideSentence_eq_true_iff.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerDecision.Audit_decideSentence_eq_true_iff.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ _ p => Formula.decideSentence p) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerDecision,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_decideSentence_eq_true_iff

end Reg.D5.S0.Computability.PresburgerDecision
