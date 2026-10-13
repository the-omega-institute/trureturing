import D5.S0.Computability.PresburgerNormalForm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.PresburgerNormalForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PresburgerArithmetic


namespace Audit_eval_negate
abbrev signature : Signature where
  Params := Atom
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => a.negate.eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (a : Atom) (xs : List Int), F.readout () a xs = !a.eval xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Atom.eval_negate)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Atom.eval_negate)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (.le (.const (-1))) []
  change false = true at hh
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Atom.eval_negate)) where
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
    refine ⟨Atom.le (Affine.consCoeff 1 (.const 0)),[0],[-1],?_⟩
    change (Atom.le (Affine.consCoeff 1 (.const 0))).negate.eval [0] ≠ (Atom.le (Affine.consCoeff 1 (.const 0))).negate.eval [-1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Atom.eval_negate)
      (type_of% (realize signature (fun _ a xs => a.negate.eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerNormalForm.Audit_eval_negate.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerNormalForm.Audit_eval_negate.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => a.negate.eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerNormalForm,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_negate

namespace Audit_eval_ofPolarity
abbrev signature : Signature where
  Params := Σ _b : Bool, QF
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => DNF.eval (DNF.ofPolarity a.1 a.2) xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (b : Bool) (p : QF) (xs : List Int), F.readout () ⟨b,p⟩ xs = if b then p.eval xs else !p.eval xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.DNF.eval_ofPolarity)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.DNF.eval_ofPolarity)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h true .truth []
  change false = true at hh
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.DNF.eval_ofPolarity)) where
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
    refine ⟨⟨true,QF.atom (.le (Affine.consCoeff 1 (.const 0)))⟩,[0],[-1],?_⟩
    change DNF.eval (DNF.ofPolarity true (.atom (.le (Affine.consCoeff 1 (.const 0))))) [0] ≠ DNF.eval (DNF.ofPolarity true (.atom (.le (Affine.consCoeff 1 (.const 0))))) [-1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.DNF.eval_ofPolarity)
      (type_of% (realize signature (fun _ a xs => DNF.eval (DNF.ofPolarity a.1 a.2) xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerNormalForm.Audit_eval_ofPolarity.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerNormalForm.Audit_eval_ofPolarity.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => DNF.eval (DNF.ofPolarity a.1 a.2) xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerNormalForm,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_ofPolarity

namespace Audit_eval_toQF
abbrev signature : Signature where
  Params := DNF
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p xs => (DNF.toQF p).eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : DNF) (xs : List Int), F.readout () p xs = DNF.eval p xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.DNF.eval_toQF)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.DNF.eval_toQF)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h [[]] []
  change false = true at hh
  cases hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.DNF.eval_toQF)) where
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
    refine ⟨[[Atom.le (Affine.consCoeff 1 (.const 0))]],[0],[-1],?_⟩
    change (DNF.toQF [[Atom.le (Affine.consCoeff 1 (.const 0))]]).eval [0] ≠ (DNF.toQF [[Atom.le (Affine.consCoeff 1 (.const 0))]]).eval [-1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.DNF.eval_toQF)
      (type_of% (realize signature (fun _ p xs => (DNF.toQF p).eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerNormalForm.Audit_eval_toQF.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerNormalForm.Audit_eval_toQF.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ p xs => (DNF.toQF p).eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerNormalForm,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_toQF

end Reg.D5.S0.Computability.PresburgerNormalForm
