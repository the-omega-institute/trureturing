import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.ThreeWayBalance
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ThreeWayBalance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.ThreeWayBalance

noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ A : Type u, A → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [AddCommGroup A] (U : A →+ A) (q : A → ℝ)
    (_hq : ∀ x, 0 ≤ q x)
    (_hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y),
    (∀ x, R.readout () ⟨A, q⟩ (U x) = q x) ∧
    (∀ z y, q (z + (y + U y + U (U y))) = q z) ∧
    (∀ x, q (-x) = q x) ∧
    (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) ∧
    ∃ Q : QuadraticMap ℤ A ℝ, ∀ x, Q x = q x

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (A := ULift.{u} ℤ) 0 (fun _ => 0)
    (by intro x; exact le_rfl) (by intro x y; norm_num)).1 0
  change (0 : ℝ) + 1 = 0 at hh
  norm_num at hh

def evidence : Registration arena.{u}
    (type_of% @_root_.D5.S3.QuadraticForms.ThreeWayBalance.three_way_quadratic_structure.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_way_quadratic_structure.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℝ, ULift.down⟩, ⟨0⟩, ⟨1⟩, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuadraticForms.ThreeWayBalance.three_way_quadratic_structure.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.ThreeWayBalance.unit
  realizationName := `Reg.D5.S3.QuadraticForms.ThreeWayBalance.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ThreeWayBalance
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.ThreeWayBalance
