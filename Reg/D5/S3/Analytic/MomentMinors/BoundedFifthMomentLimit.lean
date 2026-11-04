import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
import Reg.Support.DependentFamily

/-! Source-bound audit of the sharp one-sided fifth-moment bounds. -/

namespace Reg.D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit

open MeasureTheory ProbabilityTheory
open _root_.D5.S3.Analytic.MomentMinors.Defs (mean)
open _root_.D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the extremal standardized fifth moment at its dimensionless parameter. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => fifthBound z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Both inequalities are retained; the lower extremal bound is the selected observation. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    Integrable (fun x : ℝ => |x| ^ 5) μ → 0 < centralMoment id 2 μ →
    (∀ L : ℝ, (∀ᵐ x ∂μ, L ≤ x) →
      r.readout () () (Real.sqrt (centralMoment id 2 μ) / (mean μ - L)) ≤
        centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5) ∧
    (∀ U : ℝ, (∀ᵐ x ∂μ, x ≤ U) →
      centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 ≤
        -fifthBound (Real.sqrt (centralMoment id 2 μ) / (U - mean μ)))

private def symmetricLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

private theorem symmetricLaw_integrable (f : ℝ → ℝ) : Integrable f symmetricLaw := by
  apply Integrable.smul_measure _ (by norm_num)
  exact (integrable_dirac (by finiteness)).add_measure (integrable_dirac (by finiteness))

private theorem symmetricLaw_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂symmetricLaw) = (f (-1) + f 1) / 2 := by
  rw [symmetricLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by finiteness))
      (integrable_dirac (by finiteness))]
  simp only [integral_dirac, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private instance : IsProbabilityMeasure symmetricLaw := by
  constructor
  norm_num [symmetricLaw, Measure.smul_apply, Measure.add_apply]
  exact ENNReal.inv_two_add_inv_two

private theorem symmetricLaw_mean : mean symmetricLaw = 0 := by
  unfold mean
  rw [symmetricLaw_integral]
  norm_num

private theorem symmetricLaw_second : centralMoment id 2 symmetricLaw = 1 := by
  unfold centralMoment
  change (∫ x : ℝ, (x - mean symmetricLaw) ^ 2 ∂symmetricLaw) = 1
  rw [symmetricLaw_mean, symmetricLaw_integral]
  norm_num

private theorem symmetricLaw_fifth : centralMoment id 5 symmetricLaw = 0 := by
  unfold centralMoment
  change (∫ x : ℝ, (x - mean symmetricLaw) ^ 5 ∂symmetricLaw) = 0
  rw [symmetricLaw_mean, symmetricLaw_integral]
  norm_num

private theorem symmetricLaw_lower : ∀ᵐ x ∂symmetricLaw, (-1 : ℝ) ≤ x := by
  apply Measure.ae_smul_measure
  rw [ae_add_measure_iff]
  constructor <;> simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h symmetricLaw (symmetricLaw_integrable _) (by
    rw [symmetricLaw_second]
    norm_num)).1 (-1) symmetricLaw_lower
  norm_num [rejected, realize, symmetricLaw_fifth] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change fifthBound 1 ≠ fifthBound 2
  norm_num [fifthBound]

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
      (@_root_.D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.unit
  realizationName := `Reg.D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => fifthBound z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
    definition := some {
      owner := `D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
      name := `D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"]
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
end Reg.D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
