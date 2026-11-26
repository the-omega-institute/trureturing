import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.FejerRelativeLocalization

/-! Dependence of the relative cutoff bound on the angular Fejer kernel. -/

namespace Reg.D5.S3.Fourier.Concentration.FejerRelativeLocalization

open Finset MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FejerRelativeLocalization
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open _root_.D5.S3.Analytic.Fourier.AngularFejerKernel
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => K z.1 z.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ z => (Icc (129:ℝ) 130).indicator (fun _ => (1:ℝ)) z.2) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1,0), (2,0), ?_⟩
  change K 1 0 ≠ K 2 0
  simp [K]
  have hp := Real.pi_pos
  field_simp
  norm_num

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J]
    (g w : J → ℝ), (∀ j, 0 ≤ w j) → ∀ (p : ℕ) {η r : ℝ},
    0 < η → 1 ≤ η*r →
    let kernel := R.readout () ()
    let f := fun t => ‖complexScore g w t‖^(2*p)
    let M := ∫ t : ℝ, kernel (η,t)*f t
    M - (∫ t in -r..r, kernel (η,t)*f t) ≤ (64/(η*r))*M

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) 0 (η := 1) (r := 128) (by norm_num) (by norm_num)
  simp only [rejected,realize,Nat.mul_zero,pow_zero,mul_one] at h
  have hfull : (∫ t : ℝ, (Icc (129:ℝ) 130).indicator (fun _ => (1:ℝ)) t) = 1 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    norm_num [Real.volume_Icc]
  have hcentral : (∫ t in -(128:ℝ)..128, (Icc (129:ℝ) 130).indicator (fun _ => (1:ℝ)) t) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ (128:ℝ) := by simpa [uIcc_of_le (by norm_num : -(128:ℝ)≤128)] using ht.2
    exact indicator_of_notMem (fun hm => by linarith [hm.1]) _
  rw [hfull,hcentral] at h
  norm_num at h

def evidence : Registration arena.{u} (type_of% @relative_fejer_truncation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relative_fejer_truncation.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@relative_fejer_truncation.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerRelativeLocalization.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerRelativeLocalization.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerRelativeLocalization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Fourier.Concentration.FejerRelativeLocalization
