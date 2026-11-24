import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.SuHuTable41
import Reg.Support.DependentFamily

/-! Source-bound audits of the literal law's positive cell probabilities. -/

namespace Reg.D5.S3.Analytic.Probability.SuHuTable41

open _root_.D5.S3.Analytic.Probability
open FiniteNegativeRegression SuHuTable41
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped ENNReal
noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ a b => a < b) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem cmp_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (lt_irrefl (1 : ℝ≥0∞)) ((congrFun h 1).mp zero_lt_one)

private abbrev attainmentArena : Arena where
  signature := signature
  Law r := (∀ x : State, r.readout () () 0 (tablePMF x)) ∧
    marginalProduct tablePMF = 81 ∧ FullNRD tablePMF ∧ ¬ NA tablePMF

private theorem attainment_rejected : ¬ attainmentArena.Law rejected :=
  fun h => h.1 (fun _ => 0)

def attainmentRealization : Registration attainmentArena (type_of% table_attainment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨table_attainment, rejected, attainment_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, attainment_rejected⟩, fun e => nomatch e⟩
  dependence := cmp_dependence

def attainmentRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      table_attainment (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.SuHuTable41.attainmentUnit
  realizationName := `Reg.D5.S3.Analytic.Probability.SuHuTable41.attainmentRealization
  realizationSource := none
  generated := false
  arena := .source ⟨attainmentArena⟩
  objectArena := .source ⟨attainmentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source attainmentArena ⟨attainmentRealization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.SuHuTable41
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev covarianceArena : Arena where
  signature := signature
  Law r := (∀ x : State, r.readout () () 0 (tablePMF x)) ∧
    ∃ (I J : Finset (Fin 4)), Disjoint I J ∧
      ∃ (f : (I → Fin 3) → ℝ) (g : (J → Fin 3) → ℝ),
        Monotone f ∧ Monotone g ∧ cov tablePMF (f ∘ project I) (g ∘ project J) =
          1141067 / 9999800001 ∧ 0 < cov tablePMF (f ∘ project I) (g ∘ project J)

private theorem covariance_rejected : ¬ covarianceArena.Law rejected :=
  fun h => h.1 (fun _ => 0)

def covarianceRealization :
    Registration covarianceArena (type_of% table_positive_covariance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨table_positive_covariance, rejected, covariance_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, covariance_rejected⟩, fun e => nomatch e⟩
  dependence := cmp_dependence

def covarianceRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      table_positive_covariance (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.SuHuTable41.covarianceUnit
  realizationName := `Reg.D5.S3.Analytic.Probability.SuHuTable41.covarianceRealization
  realizationSource := none
  generated := false
  arena := .source ⟨covarianceArena⟩
  objectArena := .source ⟨covarianceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source covarianceArena ⟨covarianceRealization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.SuHuTable41
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Analytic.Probability.SuHuTable41
