import D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.ULift
import Reg.Support.DependentFamily

/-! Source-bound observation of the ordered arc at a fixed first endpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration

open _root_.D5.S0.Certificates.Algebra.MekeraNilpotentAdjacencyRefutation (arc)
open _root_.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration (arc_iff_rank)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open OmegaMath.MatrixAnnihilatorRank (nonzero_annihilator_iff_det_eq_zero)
open LeanInformationAudit

universe u

private abbrev Mat (F : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) F

private abbrev signature : Signature where
  Params := Σ F : Type u, Σ _ : Field F, Σ n : ℕ, Mat F n
  State p := Mat p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ ⟨F, field, n, A⟩ B => by
    letI : Field F := field
    exact arc A B) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law S := ∀ {F : Type u} [Field F] (n : ℕ) (_hn : 2 ≤ n) (A B : Mat F n)
    (_hne : A ≠ B) (_hA : A ≠ 0 ∧ A.det = 0) (_hB : B ≠ 0 ∧ B.det = 0),
    S.readout () ⟨F, inferInstance, n, A⟩ B ↔
      ((A * B).rank < A.rank ∧ (A * B).rank < (Matrix.fromCols (A * B) B).rank) ∨
      ((A * B).rank < B.rank ∧ (A * B).rank < (Matrix.fromRows (A * B) A).rank)

private abbrev F₂ := ULift.{u} (ZMod 2)
private abbrev first : Mat F₂.{u} 2 := Matrix.single 0 0 1
private abbrev second : Mat F₂.{u} 2 := Matrix.single 1 1 1

private theorem arc_first_second : arc (first : Mat F₂.{u} 2) second := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 := Ne.symm h01
  have hAB : (first : Mat F₂.{u} 2) * second = 0 :=
    Matrix.single_mul_single_of_ne 1 0 0 1 h01 1
  have hA : (first : Mat F₂.{u} 2) ≠ 0 := by
    intro h
    exact one_ne_zero (by simpa [first] using congrFun (congrFun h 0) 0 : (1 : F₂.{u}) = 0)
  have hB : (second : Mat F₂.{u} 2) ≠ 0 := by
    intro h
    exact one_ne_zero (by simpa [second] using congrFun (congrFun h 1) 1 : (1 : F₂.{u}) = 0)
  have hne : (first : Mat F₂.{u} 2) ≠ second := by
    intro h
    exact one_ne_zero (by simpa [first, second, Matrix.single_apply_of_row_ne h10] using
      congrFun (congrFun h 0) 0 : (1 : F₂.{u}) = 0)
  exact ⟨⟨hA, second, hB, Or.inl hAB⟩, ⟨hB, first, hA, Or.inr hAB⟩, hne,
    Or.inl ⟨1, by simp [hAB], by simpa only [one_mul] using hA,
      by simpa only [one_mul] using hB⟩⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hArc := arc_first_second.{u}
  have hA := (nonzero_annihilator_iff_det_eq_zero _).mp hArc.1
  have hB := (nonzero_annihilator_iff_det_eq_zero _).mp hArc.2.1
  have hRanks := (arc_iff_rank 2 le_rfl _ _ hArc.2.2.1 hA hB).mp hArc
  exact (h 2 le_rfl _ _ hArc.2.2.1 hA hB).mpr hRanks

private theorem varies : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨F₂.{u}, inferInstance, 2, first⟩, second, first, ?_⟩
  change arc (first : Mat F₂.{u} 2) second ≠ arc first first
  intro h
  exact (h.mp arc_first_second).2.2.1 rfl

private def evidence : Registration arena.{u} (type_of% @arc_iff_rank.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@arc_iff_rank.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := varies

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@arc_iff_rank.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration.arc_iff_rank.audit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ⟨F, field, n, A⟩ B => by
    letI : Field F := field
    exact arc A B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
