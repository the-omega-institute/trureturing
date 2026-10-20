import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.SinhLogIntegral
import Reg.Support.SingleDependentReadout

open Set MeasureTheory
open _root_.D5.S3.Analytic.Fourier.SinhLogIntegral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Fourier.SinhLogIntegral

abbrev scalarSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

abbrev pairSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def scaleActual : Realization scalarSignature :=
  realize scalarSignature (fun _ a s => h a s) (fun e => nomatch e)

def weightActual : Realization scalarSignature :=
  realize scalarSignature (fun _ a s => min 1 (s ^ 2) * h a s / s) (fun e => nomatch e)

def logActual : Realization scalarSignature :=
  realize scalarSignature (fun _ a t => Real.log (E a t)) (fun e => nomatch e)

def integrandActual : Realization pairSignature :=
  realize pairSignature (fun _ p s => (1 - Real.cos (p.2 * s)) * h p.1 s / s)
    (fun e => nomatch e)

def zeroReadout : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => 0) (fun e => nomatch e)

def oneReadout : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => 1) (fun e => nomatch e)

def pairOneReadout : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem density_one_pos : 0 < h 1 1 := by
  unfold h
  exact one_div_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr
    (by simpa using Real.pi_pos)))

private theorem log_one_pos : 0 < Real.log (E 1 1) := by
  apply Real.log_pos
  simpa [E] using Real.self_lt_sinh_iff.mpr (show (0 : ℝ) < 1 by norm_num)

private theorem scale_dependence : ObservationalDependence scalarSignature scaleActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  simpa [scaleActual, realize, h] using ne_of_lt density_one_pos

private theorem weight_dependence : ObservationalDependence scalarSignature weightActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  simpa [weightActual, realize, h] using ne_of_lt density_one_pos

private theorem log_dependence : ObservationalDependence scalarSignature logActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  simpa [logActual, realize, E] using ne_of_lt log_one_pos

private theorem integrand_dependence : ObservationalDependence pairSignature integrandActual := by
  intro i
  refine ⟨⟨1, Real.pi⟩, 0, 1, ?_⟩
  have hp : 0 < 2 * h 1 1 := mul_pos (by norm_num) density_one_pos
  simpa [integrandActual, realize] using ne_of_lt hp

abbrev scaleArena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b s : ℝ}, 0 < a → a ≤ b → 0 < s →
    b / a * h a s ≤ R.readout () b s

private theorem scale_rejected : ¬ scaleArena.Law zeroReadout := by
  intro H
  have he := @H 1 1 1 (by norm_num) le_rfl (by norm_num)
  have hp : 0 < h 1 1 := by
    unfold h
    apply one_div_pos.mpr
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by simpa using Real.pi_pos))
  change 1 / 1 * h 1 1 ≤ 0 at he
  norm_num at he
  exact (not_le_of_gt hp) he

def scaleFamily : Registration scaleArena (type_of% @h_scale_le) where
  actual := scaleActual
  bridge := Iff.rfl
  variation := ⟨h_scale_le, zeroReadout, scale_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    scaleArena.Law scaleActual zeroReadout scale_rejected
  dependence := scale_dependence

abbrev weightArena : Arena where
  signature := scalarSignature
  Law R := ∀ {a : ℝ}, 0 < a →
    IntegrableOn (fun s => R.readout () a s) (Ioi 0)

private theorem weight_rejected : ¬ weightArena.Law oneReadout := by
  intro H
  have he := @H 1 (by norm_num)
  change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ)) at he
  simpa using he

def weightFamily : Registration weightArena (type_of% @integrable_levyWeight) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨integrable_levyWeight, oneReadout, weight_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    weightArena.Law weightActual oneReadout weight_rejected
  dependence := weight_dependence

abbrev integrandArena : Arena where
  signature := pairSignature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ t : ℝ,
    IntegrableOn (fun s => R.readout () ⟨a, t⟩ s) (Ioi 0)

private theorem integrand_rejected : ¬ integrandArena.Law pairOneReadout := by
  intro H
  have he := @H 1 (by norm_num) 0
  change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ)) at he
  simpa using he

def integrandFamily : Registration integrandArena (type_of% @integrable_logIntegrand) where
  actual := integrandActual
  bridge := Iff.rfl
  variation := ⟨integrable_logIntegrand, pairOneReadout, integrand_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrandArena.Law integrandActual pairOneReadout integrand_rejected
  dependence := integrand_dependence

abbrev logArena : Arena where
  signature := scalarSignature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ t : ℝ,
    R.readout () a t =
      2 * ∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) * h a s / s

private theorem log_rejected : ¬ logArena.Law oneReadout := by
  intro H
  have he := @H 1 (by norm_num) 0
  norm_num [oneReadout, realize] at he

def logFamily : Registration logArena (type_of% @log_E_eq_integral) where
  actual := logActual
  bridge := Iff.rfl
  variation := ⟨log_E_eq_integral, oneReadout, log_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    logArena.Law logActual oneReadout log_rejected
  dependence := log_dependence

def scaleAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@h_scale_le) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.scaleUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.scaleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scaleArena⟩
  objectArena := .source ⟨scaleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scaleArena ⟨scaleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a s => h a s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.SinhLogIntegral
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scaleAudit

def weightAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_levyWeight) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.weightUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.weightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a s => min 1 (s ^ 2) * h a s / s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.SinhLogIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightAudit

def integrandAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_logIntegrand) (Realization pairSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.integrandUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.integrandFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrandArena⟩
  objectArena := .source ⟨integrandArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrandArena ⟨integrandFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ p s => (1 - Real.cos (p.2 * s)) * h p.1 s / s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.SinhLogIntegral
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms integrandAudit

def logAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_E_eq_integral) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.logUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.logFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logArena⟩
  objectArena := .source ⟨logArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logArena ⟨logFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a t => Real.log (E a t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.SinhLogIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms logAudit



namespace DensityPositive
abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a s : ℝ}, 0 < a → 0 < s → 0 < R.readout () a s
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro H
  have hn := @H 1 1 (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hn
def family : Registration arena (type_of% @h_pos) where
  actual := scaleActual
  bridge := Iff.rfl
  variation := ⟨@h_pos, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law scaleActual zeroReadout rejected_law
  dependence := scale_dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@h_pos) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.DensityPositive.unit
  realizationName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.DensityPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a t => h a t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.SinhLogIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DensityPositive

def profileActual : Realization scalarSignature :=
  realize scalarSignature (fun _ a t => E a t) (fun e => nomatch e)
private theorem profile_dependence : ObservationalDependence scalarSignature profileActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  have hp : 1 < E 1 1 := by
    simpa [E] using Real.self_lt_sinh_iff.mpr (show (0 : ℝ) < 1 by norm_num)
  simpa [profileActual, realize, E] using ne_of_lt hp

namespace ProfilePositive
abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ t : ℝ, 0 < R.readout () a t
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro H
  have hn := @H 1 (by norm_num) 0
  exact (lt_irrefl (0 : ℝ)) hn
def family : Registration arena (type_of% @E_pos) where
  actual := profileActual
  bridge := Iff.rfl
  variation := ⟨@E_pos, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law profileActual zeroReadout rejected_law
  dependence := profile_dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@E_pos) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.ProfilePositive.unit
  realizationName := `Reg.D5.S3.Analytic.Fourier.SinhLogIntegral.ProfilePositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a t => E a t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.SinhLogIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ProfilePositive

end Reg.D5.S3.Analytic.Fourier.SinhLogIntegral
