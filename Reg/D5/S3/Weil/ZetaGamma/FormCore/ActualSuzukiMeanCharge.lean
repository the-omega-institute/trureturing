import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
import Reg.Support.SingleDependentReadout

open MeasureTheory Set
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge

private def zeroSource : ℝ → ℂ := fun _ => 0

private theorem zero_h6 : originalPhysicalH6 zeroSource := by
  constructor
  · exact MemLp.zero'
  · simp [zeroSource]

private theorem zero_profile : actualGammaProfile zeroSource = fun _ => 0 := by
  funext t
  simp [zeroSource, actualGammaProfile, fullTheta, physicalTerm]

private theorem zero_charge : actualSuzukiMeanCharge zeroSource = 0 := by
  simp [actualSuzukiMeanCharge, actualSuzukiEvenBProfile, actualSuzukiBProfile,
    zero_profile, rightExponentialTail]

namespace Formula

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ t z => (actualSuzukiMeanKernel t : ℂ) * z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ t _ => (Real.exp (-t) : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F),
    Integrable (actualSuzukiEvenBProfile F) volume ∧
      actualSuzukiMeanCharge F = ∫ t : ℝ in Ioi 0, R.readout () t (actualGammaProfile F t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h zeroSource zero_h6).2
  change actualSuzukiMeanCharge zeroSource = ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) at hh
  rw [zero_charge, integral_complex_ofReal] at hh
  have hi : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  rw [hi] at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (actualSuzukiMeanKernel 0 : ℂ) * 0 ≠ (actualSuzukiMeanKernel 0 : ℂ) * 1
  norm_num [actualSuzukiMeanKernel]

def family : Registration arena (type_of% actual_h6_suzuki_mean_charge_formula) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_h6_suzuki_mean_charge_formula, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_h6_suzuki_mean_charge_formula (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.Formula.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.Formula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t z => (actualSuzukiMeanKernel t : ℂ) * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Formula

namespace Norm

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F),
    R.readout () () (actualSuzukiMeanCharge F) ≤ ∫ t : ℝ in Ioi 0, ‖actualGammaProfile F t‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h zeroSource zero_h6
  change (1 : ℝ) ≤ ∫ t : ℝ in Ioi 0, ‖actualGammaProfile zeroSource t‖ at hh
  norm_num [zero_profile] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def family : Registration arena (type_of% actual_h6_suzuki_mean_charge_norm_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_h6_suzuki_mean_charge_norm_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_h6_suzuki_mean_charge_norm_le (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.Norm.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.Norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Norm

namespace Imaginary

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ z => z.im) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F)
    (_hreal : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), (actualGammaProfile F t).im = 0),
    R.readout () () (actualSuzukiMeanCharge F) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), (actualGammaProfile zeroSource t).im = 0 := by
    simp [zero_profile]
  have hh := h zeroSource zero_h6 hz
  change (1 : ℝ) = 0 at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Complex.I, ?_⟩
  change (0 : ℂ).im ≠ Complex.I.im
  norm_num

def family : Registration arena (type_of% actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.Imaginary.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.Imaginary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Imaginary

namespace ProfileLinear

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ a z => a * z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F G H : ℝ → ℂ) (_hF : originalPhysicalH6 F) (_hG : originalPhysicalH6 G)
    (_hH : originalPhysicalH6 H) (a b : ℂ)
    (_hprofile : actualGammaProfile H =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => a * actualGammaProfile F t + b * actualGammaProfile G t)),
    actualSuzukiMeanCharge H = R.readout () a (actualSuzukiMeanCharge F) +
      b * actualSuzukiMeanCharge G

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : actualGammaProfile zeroSource =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (0 : ℂ) * actualGammaProfile zeroSource t +
        (0 : ℂ) * actualGammaProfile zeroSource t) := by simp [zero_profile]
  have hh := h zeroSource zeroSource zeroSource zero_h6 zero_h6 zero_h6 0 0 hz
  change actualSuzukiMeanCharge zeroSource = (1 : ℂ) + 0 * actualSuzukiMeanCharge zeroSource at hh
  simp [zero_charge] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (1 : ℂ) * 0 ≠ (1 : ℂ) * 1
  norm_num

def family : Registration arena (type_of% actual_h6_suzuki_mean_charge_linear_of_profile_ae) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_h6_suzuki_mean_charge_linear_of_profile_ae, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_h6_suzuki_mean_charge_linear_of_profile_ae (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.ProfileLinear.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.ProfileLinear.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a z => a * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProfileLinear

namespace SourceLinear

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature := realize signature (fun _ a z => a * z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F G : ℝ → ℂ) (_hF : originalPhysicalH6 F) (_hG : originalPhysicalH6 G)
    (a b : ℂ) (_hH : originalPhysicalH6 (fun x => a * F x + b * G x)),
    actualSuzukiMeanCharge (fun x => a * F x + b * G x) =
      R.readout () a (actualSuzukiMeanCharge F) + b * actualSuzukiMeanCharge G

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsrc : (fun x => (0 : ℂ) * zeroSource x + (0 : ℂ) * zeroSource x) = zeroSource := by
    funext x
    simp [zeroSource]
  have hz : originalPhysicalH6 (fun x => (0 : ℂ) * zeroSource x + (0 : ℂ) * zeroSource x) := by
    rw [hsrc]
    exact zero_h6
  have hh := h zeroSource zeroSource zero_h6 zero_h6 0 0 hz
  change actualSuzukiMeanCharge (fun x => (0 : ℂ) * zeroSource x + (0 : ℂ) * zeroSource x) =
    (1 : ℂ) + 0 * actualSuzukiMeanCharge zeroSource at hh
  rw [hsrc, zero_charge] at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (1 : ℂ) * 0 ≠ (1 : ℂ) * 1
  norm_num

def family : Registration arena (type_of% actual_h6_suzuki_mean_charge_linear) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_h6_suzuki_mean_charge_linear, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_h6_suzuki_mean_charge_linear (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.SourceLinear.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge.SourceLinear.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a z => a * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SourceLinear

end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
