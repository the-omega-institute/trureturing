import D5.S0.Computability.PresburgerSyntax
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.PresburgerSyntax
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PresburgerArithmetic


namespace Audit_eval_neg
abbrev signature : Signature where
  Params := Affine
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ t xs => t.neg.eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (t : Affine) (xs : List Int), F.readout () t xs = -t.eval xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Affine.eval_neg)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Affine.eval_neg)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (.const 1) []
  change (0 : Int) = -1 at hh
  norm_num at hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Affine.eval_neg)) where
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
    refine ⟨Affine.consCoeff 1 (.const 0),[0],[1],?_⟩
    change (Affine.consCoeff 1 (.const 0)).neg.eval [0] ≠ (Affine.consCoeff 1 (.const 0)).neg.eval [1]
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Affine.eval_neg)
      (type_of% (realize signature (fun _ t xs => t.neg.eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerSyntax.Audit_eval_neg.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerSyntax.Audit_eval_neg.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ t xs => t.neg.eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerSyntax,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_neg

namespace Audit_eval_add
abbrev signature : Signature where
  Params := Σ _s : Affine, Affine
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => (a.1.add a.2).eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (s t : Affine) (xs : List Int), F.readout () ⟨s,t⟩ xs = s.eval xs + t.eval xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Affine.eval_add)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Affine.eval_add)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (.const 1) (.const 0) []
  change (0 : Int) = 1 at hh
  norm_num at hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Affine.eval_add)) where
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
    refine ⟨⟨Affine.consCoeff 1 (.const 0), .const 0⟩,[0],[1],?_⟩
    change ((Affine.consCoeff 1 (.const 0)).add (.const 0)).eval [0] ≠ ((Affine.consCoeff 1 (.const 0)).add (.const 0)).eval [1]
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Affine.eval_add)
      (type_of% (realize signature (fun _ a xs => (a.1.add a.2).eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerSyntax.Audit_eval_add.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerSyntax.Audit_eval_add.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => (a.1.add a.2).eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerSyntax,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_add

namespace Audit_eval_scale
abbrev signature : Signature where
  Params := Σ _k : Int, Affine
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => (a.2.scale a.1).eval xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (k : Int) (t : Affine) (xs : List Int), F.readout () ⟨k,t⟩ xs = k * t.eval xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.Affine.eval_scale)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.Affine.eval_scale)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 1 (.const 1) []
  change (0 : Int) = 1 at hh
  norm_num at hh

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.Affine.eval_scale)) where
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
    refine ⟨⟨1,Affine.consCoeff 1 (.const 0)⟩,[0],[1],?_⟩
    change ((Affine.consCoeff 1 (.const 0)).scale 1).eval [0] ≠ ((Affine.consCoeff 1 (.const 0)).scale 1).eval [1]
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.Affine.eval_scale)
      (type_of% (realize signature (fun _ a xs => (a.2.scale a.1).eval xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerSyntax.Audit_eval_scale.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerSyntax.Audit_eval_scale.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => (a.2.scale a.1).eval xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerSyntax,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_scale

end Reg.D5.S0.Computability.PresburgerSyntax
