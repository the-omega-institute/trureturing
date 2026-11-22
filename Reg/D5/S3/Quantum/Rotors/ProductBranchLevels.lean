import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Rotors.ProductBranchLevels
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.NormNum

/-! Moving the higher coefficient changes the ordered branch reading. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Rotors.ProductBranchLevels
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Rotors.ProductBranchLevels
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ x => x + 1) (fun e => nomatch e)

namespace Levels

def arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ} (ha : 0 < a) (hab : a ≤ R.readout () () b),
    IsLeast (above a b 0) (3 * a) ∧ IsLeast (above a b (3 * a)) (secondLevel a b)

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have h := (law (a := 1) (b := 0) (by norm_num) (by change (1 : ℝ) ≤ 0 + 1; norm_num)).2.1.1
  norm_num [secondLevel] at h

def family : Registration arena (type_of% @first_two_positive_levels) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_two_positive_levels, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), (zero_ne_one : (0 : ℝ) ≠ 1)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Rotors.ProductBranchLevels.first_two_positive_levels)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Rotors.ProductBranchLevels.Levels.unit
  realizationName := `Reg.D5.S3.Quantum.Rotors.ProductBranchLevels.Levels.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Rotors.ProductBranchLevels
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Levels

namespace Fiber

def arena : Arena where
  signature := signature
  Law R := ∀ {a b c : ℝ} (ha : 0 < a),
    secondLevel a (R.readout () () b) = secondLevel a c ↔
      b = c ∨ (b = a ∧ c = 2 * a) ∨ (c = a ∧ b = 2 * a) ∨
      (8 * a ≤ 3 * b ∧ 8 * a ≤ 3 * c)

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have h := (law (a := 1) (b := 2) (c := 2) (by norm_num)).mpr (Or.inl rfl)
  change secondLevel 1 (2 + 1) = secondLevel 1 2 at h
  norm_num [secondLevel] at h

def family : Registration arena (type_of% @second_level_fiber) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨second_level_fiber, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), (zero_ne_one : (0 : ℝ) ≠ 1)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Rotors.ProductBranchLevels.second_level_fiber)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Rotors.ProductBranchLevels.Fiber.unit
  realizationName := `Reg.D5.S3.Quantum.Rotors.ProductBranchLevels.Fiber.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Rotors.ProductBranchLevels
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Fiber

end
end Reg.D5.S3.Quantum.Rotors.ProductBranchLevels
