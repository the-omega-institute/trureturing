import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open scoped BigOperators
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
universe u

/-- A centered real observation is read through the square function. -/
@[reducible] def squareSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def squareActual : Realization squareSignature.{u} :=
  realize squareSignature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def squareRejected : Realization squareSignature.{u} :=
  realize squareSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- The full source telescope uses the selected square only in its moment hypothesis. -/
@[reducible] def squareArena : Arena where
  signature := squareSignature.{u}
  Law R := ∀ {Ω : Type u} [Fintype Ω] (p X : Ω → ℝ)
    (a h B : ℝ) (_hp : ∀ o, 0 ≤ p o) (_hh : 0 < h)
    (_hB : (∑ o, p o * R.readout ⟨()⟩ () (X o - a)) ≤ B),
    (∑ o, if h < |X o - a| then p o else 0) ≤ B / h ^ 2

theorem square_actual_law : squareArena.{u}.Law squareActual.{u} :=
  finite_square_markov

theorem square_rejected_law : ¬ squareArena.{u}.Law squareRejected.{u} := by
  classical
  intro h
  have hc := h (Ω := ULift.{u} Unit) (fun _ => (1 : ℝ)) (fun _ => 2) 0 1 (-1)
    (by intro o; norm_num) (by norm_num) (by simp [squareRejected, realize])
  norm_num at hc

def squareEvidence : Registration squareArena.{u} (squareArena.Law squareActual) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨square_actual_law, squareRejected, square_rejected_law⟩
  sensitivity := ⟨fun i => ⟨squareRejected,
      fun j h => (h (Subsingleton.elim j i)).elim, rfl, square_rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 2 ≠ 1 ^ 2
    norm_num

noncomputable def square_registration.{u_1} : LeanInformationAudit.Contract.Registration
    (@D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.finite_square_markov.{u_1})
    (type_of% (realize squareSignature.{u_1} (fun _ _ x => x ^ 2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.squareUnit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.squareEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨squareArena.{u_1}⟩,
  objectArena := .source ⟨squareArena.{u_1}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source squareArena.{u_1} ⟨squareEvidence.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize squareSignature.{u_1} (fun _ _ x => x ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "domain", "fn", "arg",
        "arg", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
