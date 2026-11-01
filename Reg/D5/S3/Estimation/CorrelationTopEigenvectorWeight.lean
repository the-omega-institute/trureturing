import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.CorrelationTopEigenvectorWeight
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Estimation.CorrelationTopEigenvectorWeight
open _root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the strict comparison at the source's standard-deviation coordinate. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c σ => @decide (c < σ) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- Retain the full eventual-existence statement and its domain restriction. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c σ : ℝ, domainD c σ →
    ((∃ m : ℕ, ∀ n ≥ m, ∃ a : Matrix (Fin n) (Fin n) ℝ,
      IsCorrelation a ∧ meanCorr a = c ∧ stdCorr a = σ ∧ SatisfiesWGap a) ↔
      R.readout () c σ = true)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hd : domainD (1 / 4) (1 / 4) := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    rintro (hbad | ⟨hbad, _⟩)
    · nlinarith
    · norm_num at hbad
  have hex := (h (1 / 4) (1 / 4) hd).mpr rfl
  exact (lt_irrefl (1 / 4 : ℝ)) ((result (1 / 4) (1 / 4) hd).mp hex)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [claim, actual, realize]
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.CorrelationTopEigenvectorWeight.unit
  realizationName :=
    `Reg.D5.S3.Estimation.CorrelationTopEigenvectorWeight.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ c σ => @decide (c < σ) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.CorrelationTopEigenvectorWeight
    definition := some {
      owner := `D5.S3.Estimation.CorrelationTopEigenvectorWeight
      name := `D5.S3.Estimation.CorrelationTopEigenvectorWeight.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight.result
#print _root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Estimation.CorrelationTopEigenvectorWeight
