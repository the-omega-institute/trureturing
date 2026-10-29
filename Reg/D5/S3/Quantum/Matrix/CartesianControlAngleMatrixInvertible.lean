import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
import Reg.Support.DependentFamily

/-! Source-bound audit of invertibility for Cartesian-control angle matrices. -/

namespace Reg.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible

open _root_.D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe invertibility at the matrix size determined by the original factors. -/
abbrev signature : Signature where
  Params := Σ k : ℕ, Fin k → ℕ
  State p := Matrix (Fin (∏ l, p.2 l)) (Fin (∏ l, p.2 l)) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => IsUnit M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

/-- Retain every factor, dimension and pair of enumerations in the source claim. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))),
    R.readout () ⟨k, d⟩ (angleMatrix d b g)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let d : Fin 0 → ℕ := Fin.elim0
  let e : Fin (∏ l, d l) ≃ ((l : Fin 0) → Fin (d l)) := by
    simpa using (Equiv.ofUnique (Fin 1) ((l : Fin 0) → Fin (d l)))
  exact h 0 d e e

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  change IsUnit (0 : Matrix (Fin (∏ l : Fin 0, (Fin.elim0 l : ℕ)))
    (Fin (∏ l : Fin 0, (Fin.elim0 l : ℕ))) ℝ) ≠ IsUnit 1
  letI : Nonempty (Fin (∏ l : Fin 0, (Fin.elim0 l : ℕ))) := ⟨⟨0, by simp⟩⟩
  intro h
  exact not_isUnit_zero (Eq.mpr h isUnit_one)

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
    (realize signature (fun _ _ M => IsUnit M) (fun e => nomatch e))
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
      path := #["body", "body", "body", "body"]
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
