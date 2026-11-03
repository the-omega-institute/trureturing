import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.CorrelationTopEigenvectorWeight
import Reg.Support.DependentFamily

/-! Source-bound registration of the mean-correlation coordinate in the settlement. -/

namespace Reg.D5.S3.Estimation.CorrelationTopEigenvectorWeight
open _root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the mean correlation, retaining the matrix dimension as a parameter. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => meanCorr a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the full eventual-existence statement and its domain restriction. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c σ : ℝ, domainD c σ →
    ((∃ m : ℕ, ∀ n ≥ m, ∃ a : Matrix (Fin n) (Fin n) ℝ,
      IsCorrelation a ∧ R.readout () n a = c ∧ stdCorr a = σ ∧ SatisfiesWGap a) ↔ c < σ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hd : domainD (2 / 5) (3 / 5) := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    rintro (hbad | ⟨_, hbad⟩)
    · nlinarith
    · norm_num at hbad
  obtain ⟨m, hm⟩ := (h (2 / 5) (3 / 5) hd).mpr (by norm_num)
  obtain ⟨a, _, hmean, _⟩ := hm m le_rfl
  change (0 : ℝ) = 2 / 5 at hmean
  norm_num at hmean

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, (fun _ _ => 1), ?_⟩
  change meanCorr (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ meanCorr (fun _ _ => 1)
  simp only [meanCorr, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [Matrix.one_apply]

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
    (fun _ _ a => meanCorr a) (fun e => nomatch e))
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
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "body",
        "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight.result
#print _root_.D5.S3.Estimation.CorrelationTopEigenvectorWeight.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Estimation.CorrelationTopEigenvectorWeight
