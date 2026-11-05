import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.GaussianComplexMoments
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the Gaussian density normalization identity. -/

namespace Reg.D5.S3.Fourier.Asymptotics.GaussianComplexMoments

open _root_.D5.S3.Fourier.Asymptotics.GaussianComplexMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open ProbabilityTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _μ : ℝ, {v : ℝ // 0 < v}) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p y => gaussianDensity p.1 p.2.1 y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (μ v : ℝ) (hv : 0 < v) (y : ℝ),
    R.readout () ⟨μ, ⟨v, hv⟩⟩ y = gaussianPDFReal μ (variance v hv) y

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 1 (by norm_num) 0
  change (0 : ℝ) = gaussianPDFReal 0
    (D5.S3.Fourier.Asymptotics.GaussianComplexMoments.variance 1 (by norm_num)) 0 at hbad
  have hv0 : D5.S3.Fourier.Asymptotics.GaussianComplexMoments.variance 1 (by norm_num) ≠ 0 := by
    intro hz
    have hz' := congrArg (fun t : NNReal => (t : ℝ)) hz
    change (1 : ℝ) = 0 at hz'
    norm_num at hz'
  have hpos : 0 < gaussianPDFReal 0
      (D5.S3.Fourier.Asymptotics.GaussianComplexMoments.variance 1 (by norm_num)) 0 := by
    apply ProbabilityTheory.gaussianPDFReal_pos
    exact hv0
  linarith

theorem actual_law : arena.Law actual := by
  intro μ v hv y
  exact gaussianDensity_eq_pdf μ v hv y

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, ⟨1, by norm_num⟩⟩, 0, 1, ?_⟩
  change gaussianDensity 0 1 0 ≠ gaussianDensity 0 1 1
  intro h
  simp only [gaussianDensity] at h
  have h' := congrArg (fun t : ℝ => t * Real.sqrt (2 * Real.pi * 1)) h
  field_simp at h'
  have hlt : Real.exp (-(1 / 2 : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  norm_num at h'
  linarith

def source_registration : Registration arena (type_of% @gaussianDensity_eq_pdf) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gaussianDensity_eq_pdf) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.GaussianComplexMoments.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.GaussianComplexMoments.source_registration
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
    (fun _ p y => gaussianDensity p.1 p.2.1 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.GaussianComplexMoments
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Fourier.Asymptotics.GaussianComplexMoments
