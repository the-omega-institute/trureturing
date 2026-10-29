import D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative

open _root_.D5.S3.AnalyticClosure.Polylogarithm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ+, Σ _ : List ℕ+, ℕ+
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p n ↦ CompositionReciprocalSeries.ordinaryCoefficient p.1 p.2.1 p.2.2 n)
    (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → R.readout () ⟨head, tail, ell⟩ n < 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, _, hN⟩ := h 1 [] 1
  exact (lt_irrefl (0 : ℝ)) (hN N le_rfl)

private theorem coefficient_zero_pos (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    0 < CompositionReciprocalSeries.ordinaryCoefficient head tail ell 0 := by
  simp only [CompositionReciprocalSeries.ordinaryCoefficient,
    CompositionReciprocalSeries.ordinarySeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
    map_pow, PowerSeries.constantCoeff_mk]
  exact inv_pos.mpr (pow_pos ((CompositionDisk.source_series head tail).1 0) _)

def sourceEvidence : Registration arena (type_of% (@CompositionEventualNegative.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨CompositionEventualNegative.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨N, _, hN⟩ := CompositionEventualNegative.result 1 [] 1
    refine ⟨⟨1, [], 1⟩, 0, N, ?_⟩
    change CompositionReciprocalSeries.ordinaryCoefficient 1 [] 1 0 ≠
      CompositionReciprocalSeries.ordinaryCoefficient 1 [] 1 N
    exact ne_of_gt ((hN N le_rfl).trans (coefficient_zero_pos 1 [] 1))

def result_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@CompositionEventualNegative.result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative.resultUnit
  realizationName :=
    `Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n ↦ CompositionReciprocalSeries.ordinaryCoefficient p.1 p.2.1 p.2.2 n)
    (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative
