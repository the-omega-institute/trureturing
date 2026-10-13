import D5.S0.Computability.PresburgerCooper
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.PresburgerCooper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PresburgerArithmetic


namespace Audit_le_maxFrom_left
abbrev signature : Signature where
  Params := Int
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ x xs => maxFrom x xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (x : Int) (xs : List Int), x ≤ F.readout () x xs

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.le_maxFrom_left)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.le_maxFrom_left)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 0 []
  change (0 : Int) ≤ -1 at hh
  omega

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.le_maxFrom_left)) where
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
    refine ⟨0,[],[1],?_⟩
    change maxFrom 0 [] ≠ maxFrom 0 [1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.le_maxFrom_left)
      (type_of% (realize signature (fun _ x xs => maxFrom x xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerCooper.Audit_le_maxFrom_left.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerCooper.Audit_le_maxFrom_left.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ x xs => maxFrom x xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerCooper,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_le_maxFrom_left

namespace Audit_minFrom_le_left
abbrev signature : Signature where
  Params := Int
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ x xs => minFrom x xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (x : Int) (xs : List Int), F.readout () x xs ≤ x

theorem bridge : (type_of% (@_root_.PresburgerArithmetic.minFrom_le_left)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.PresburgerArithmetic.minFrom_le_left)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 0 []
  change (1 : Int) ≤ 0 at hh
  omega

def evidence : Registration arena (type_of% (@_root_.PresburgerArithmetic.minFrom_le_left)) where
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
    refine ⟨0,[],[-1],?_⟩
    change minFrom 0 [] ≠ minFrom 0 [-1]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.PresburgerArithmetic.minFrom_le_left)
      (type_of% (realize signature (fun _ x xs => minFrom x xs) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.PresburgerCooper.Audit_minFrom_le_left.unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerCooper.Audit_minFrom_le_left.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ x xs => minFrom x xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerCooper,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_minFrom_le_left

end Reg.D5.S0.Computability.PresburgerCooper
