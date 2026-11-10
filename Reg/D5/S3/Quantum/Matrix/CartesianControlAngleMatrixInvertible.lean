import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Source-bound audit of invertibility for Cartesian-control angle matrices. -/

namespace Reg.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible

open _root_.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the unit predicate at the source matrix multiplication structure. -/
abbrev signature : Signature where
  Params := Σ k : ℕ, Fin k → ℕ
  State p := Monoid (Matrix (Fin (∏ l, p.2 l)) (Fin (∏ l, p.2 l)) ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin (∏ l, p.2 l)) (Fin (∏ l, p.2 l)) ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ monoid => @IsUnit _ monoid) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain every factor, dimension and pair of enumerations in the source claim. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))),
    R.readout () ⟨k, d⟩
      (inferInstance : Monoid (Matrix (Fin (∏ l, d l)) (Fin (∏ l, d l)) ℝ))
      (angleMatrix d b g)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let d : Fin 0 → ℕ := Fin.elim0
  let e : Fin (∏ l, d l) ≃ ((l : Fin 0) → Fin (d l)) := by
    simpa using (Equiv.ofUnique (Fin 1) ((l : Fin 0) → Fin (d l)))
  exact h 0 d e e

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let n : ℕ := ∏ l : Fin 0, (Fin.elim0 l : ℕ)
  let X := Matrix (Fin n) (Fin n) ℝ
  let : Nonempty (Fin n) := ⟨⟨0, by simp [n]⟩⟩
  let standard : Monoid X := inferInstance
  have standard_zero_not_unit : ¬ @IsUnit X standard (0 : X) := not_isUnit_zero
  let additive : Monoid X := @Multiplicative.monoid X inferInstance
  have additive_zero_unit : @IsUnit X additive (0 : X) := by
    refine ⟨⟨0, 0, ?_, ?_⟩, rfl⟩ <;>
      change (0 : X) + 0 = 0 <;>
      exact add_zero 0
  refine ⟨⟨0, Fin.elim0⟩, standard, additive, ?_⟩
  intro h
  have hz := congrFun h (0 : X)
  change @IsUnit X standard (0 : X) = @IsUnit X additive (0 : X) at hz
  exact standard_zero_not_unit (Eq.mpr hz additive_zero_unit)

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ monoid => @IsUnit _ monoid) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
    definition := some {
      owner := `D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
      name := `D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
