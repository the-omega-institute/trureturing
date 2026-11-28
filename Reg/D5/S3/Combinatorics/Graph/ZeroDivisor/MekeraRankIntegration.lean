import D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.ULift
import Reg.Support.DependentFamily

/-! Source-bound observation of the second endpoint rank. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration

open _root_.D5.S0.Certificates.Algebra.MekeraNilpotentAdjacencyRefutation (arc)
open _root_.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration (arc_iff_rank)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open OmegaMath.MatrixAnnihilatorRank (leftWitness_iff_rank nonzero_annihilator_iff_det_eq_zero)
open LeanInformationAudit

universe u

noncomputable section

private abbrev Mat (F : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) F

private abbrev signature : Signature where
  Params := Σ F : Type u, Σ _ : Field F, ℕ
  State p := Mat p.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev observe (p : signature.{u}.Params) (B : signature.State p) : ℕ :=
  letI : Field p.1 := p.2.1
  B.rank

private def actual : Realization signature.{u} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law S := ∀ {F : Type u} [Field F] (n : ℕ) (_hn : 2 ≤ n) (A B : Mat F n)
    (_hne : A ≠ B) (_hA : A ≠ 0 ∧ A.det = 0) (_hB : B ≠ 0 ∧ B.det = 0),
    arc A B ↔
      ((A * B).rank < A.rank ∧ (A * B).rank < (Matrix.fromCols (A * B) B).rank) ∨
      ((A * B).rank < S.readout () ⟨F, inferInstance, n⟩ B ∧
        (A * B).rank < (Matrix.fromRows (A * B) A).rank)

private abbrev F₂ := ULift.{u} (ZMod 2)
private abbrev unit (i j : Fin 3) : Mat F₂.{u} 3 := Matrix.single i j 1

private theorem ne_zero_of_entry {M : Mat F₂.{u} 3} {i j : Fin 3} (h : M i j = 1) :
    M ≠ 0 := by
  intro hM
  rw [hM, Matrix.zero_apply] at h
  exact zero_ne_one h

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A : Mat F₂.{u} 3 := unit 0 0 + unit 0 2
  let B : Mat F₂.{u} 3 := unit 0 0 + unit 1 1
  let T : Mat F₂.{u} 3 := unit 1 0 + unit 2 0
  have hA : A ≠ 0 := ne_zero_of_entry (i := 0) (j := 0) (by simp [A, unit])
  have hB : B ≠ 0 := ne_zero_of_entry (i := 1) (j := 1) (by simp [B, unit])
  have hne : A ≠ B := by
    intro hEq
    have hEntry := congrFun (congrFun hEq 1) 1
    simp [A, B, unit] at hEntry
  have hAV := (nonzero_annihilator_iff_det_eq_zero A).mp
    ⟨hA, unit 1 1, ne_zero_of_entry (i := 1) (j := 1) (by simp [unit]),
      Or.inl (by simp [A, unit, add_mul])⟩
  have hBV := (nonzero_annihilator_iff_det_eq_zero B).mp
    ⟨hB, unit 2 2, ne_zero_of_entry (i := 2) (j := 2) (by simp [unit]),
      Or.inl (by simp [B, unit, add_mul])⟩
  have hAB : A * B = unit 0 0 := by simp [A, B, unit, add_mul, mul_add]
  have hAT : A * T = unit 0 0 := by simp [A, T, unit, add_mul, mul_add]
  have hBT : B * T = unit 1 0 := by simp [B, T, unit, add_mul, mul_add]
  have hArc : arc A B := ⟨(nonzero_annihilator_iff_det_eq_zero A).mpr hAV,
    (nonzero_annihilator_iff_det_eq_zero B).mpr hBV, hne,
    Or.inr ⟨T, by simp [hAB, T, unit, mul_add],
      hAT.symm ▸ ne_zero_of_entry (i := 0) (j := 0) (by simp [unit]),
      hBT.symm ▸ ne_zero_of_entry (i := 1) (j := 0) (by simp [unit])⟩⟩
  rcases (h 3 (by decide) A B hne hAV hBV).mp hArc with hLeft | hRight
  · obtain ⟨S, hS, hSA, _⟩ := (leftWitness_iff_rank A B).mpr hLeft
    have hCA : (A * B) * A = A := by simp [hAB, A, unit, mul_add]
    apply hSA
    calc
      S * A = S * ((A * B) * A) := congrArg (S * ·) hCA.symm
      _ = 0 := by rw [← mul_assoc, hS, zero_mul]
  · exact Nat.not_lt_zero _ hRight.1

private theorem varies : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨F₂.{u}, inferInstance, 1⟩, 0, 1, ?_⟩
  change Matrix.rank (0 : Mat F₂.{u} 1) ≠ Matrix.rank (1 : Mat F₂.{u} 1)
  simp [Matrix.rank_zero, Matrix.rank_one]

def evidence : Registration arena.{u} (type_of% @arc_iff_rank.{u}) where
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
  readout := some (realize signature (fun _ => observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
