import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaRvm.HorizontalLogTail
import Reg.Support.SingleDependentReadout

/-! Source-bound observations for the actual principal-log zeta tail. -/

noncomputable section

namespace Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail

open Complex Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Zeta23.RvM
open _root_.ConjectureMachines.Semantics.Riemann.VonMangoldtCount
open LeanInformationAudit
open scoped Interval

local notation "q" => (Real.pi ^ 2 / 6 - 1 : ℝ)
local notation "Ctail" => (q / (1 - q))

abbrev complexSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

abbrev realSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

abbrev imSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def complexActual : Realization complexSignature :=
  realize complexSignature (fun _ _ z => Complex.log z) (fun e => nomatch e)

def realActual : Realization realSignature :=
  realize realSignature (fun _ _ x => Real.log x) (fun e => nomatch e)

def imActual : Realization imSignature :=
  realize imSignature (fun _ _ z => z.im) (fun e => nomatch e)

private lemma tailCoefficient_pos : 0 < Ctail := by
  have hp := Real.pi_gt_three
  have hq : 0 < q := by nlinarith
  have hq1 := pi_sq_div_six_sub_one_le_three_fourths
  exact div_pos hq (by linarith)

private lemma complexDependence : ObservationalDependence complexSignature complexActual := by
  intro i
  refine ⟨(), 1, -1, ?_⟩
  change Complex.log (1 : ℂ) ≠ Complex.log (-1)
  rw [Complex.log_one, Complex.log_neg_one]
  intro he
  have hi := congrArg Complex.im he
  simp only [zero_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
    mul_one, mul_zero, add_zero] at hi
  linarith [Real.pi_pos]

private lemma realDependence : ObservationalDependence realSignature realActual := by
  intro i
  refine ⟨(), 1, Real.exp 1, ?_⟩
  change Real.log 1 ≠ Real.log (Real.exp 1)
  simp

private lemma imDependence : ObservationalDependence imSignature imActual := by
  intro i
  refine ⟨(), 0, I, ?_⟩
  change (0 : ℂ).im ≠ I.im
  norm_num

def normArena : Arena where
  signature := complexSignature
  Law O := ∀ {s : ℂ} (_ : 2 ≤ s.re),
    ‖O.readout () () (riemannZeta s)‖ ≤ Ctail * (2 : ℝ) ^ (2 - s.re)

def normBad : Realization complexSignature :=
  realize complexSignature (fun _ _ _ => ((Ctail + 1 : ℝ) : ℂ)) (fun e => nomatch e)

private lemma normBad_rejected : ¬ normArena.Law normBad := by
  intro h
  have hh := h (s := (2 : ℂ)) (by norm_num)
  change ‖((Ctail + 1 : ℝ) : ℂ)‖ ≤ Ctail * (2 : ℝ) ^ (2 - (2 : ℝ)) at hh
  simp only [sub_self, Real.rpow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
  rw [abs_of_pos (by linarith [tailCoefficient_pos])] at hh
  linarith

def complexIntegrableArena : Arena where
  signature := complexSignature
  Law O := ∀ {R : ℝ} (_ : 2 ≤ R) (t : ℝ),
    IntegrableOn (fun σ : ℝ => O.readout () ()
      (riemannZeta ((σ : ℂ) + (t : ℂ) * I))) (Ioi R)

def complexIntegrableBad : Realization complexSignature :=
  realize complexSignature (fun _ _ _ => 1) (fun e => nomatch e)

private lemma complexIntegrableBad_rejected :
    ¬ complexIntegrableArena.Law complexIntegrableBad := by
  intro h
  have hh := h (R := 2) (by norm_num) 0
  change IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi (2 : ℝ)) at hh
  simp at hh

def realIntegrableArena : Arena where
  signature := realSignature
  Law O := ∀ {R : ℝ} (_ : 2 ≤ R) (t : ℝ),
    IntegrableOn (fun σ : ℝ => O.readout () ()
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) (Ioi R)

def realIntegrableBad : Realization realSignature :=
  realize realSignature (fun _ _ _ => 1) (fun e => nomatch e)

private lemma realIntegrableBad_rejected : ¬ realIntegrableArena.Law realIntegrableBad := by
  intro h
  have hh := h (R := 2) (by norm_num) 0
  change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (2 : ℝ)) at hh
  simp at hh

def logarithmBad : Realization realSignature :=
  realize realSignature (fun _ _ _ => -1) (fun e => nomatch e)

def complexBoundArena : Arena where
  signature := realSignature
  Law O := ∀ {R : ℝ} (_ : 2 ≤ R) (t : ℝ),
    (∫ σ : ℝ in Ioi R, ‖Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I))‖) ≤
      Ctail / O.readout () () 2 * (2 : ℝ) ^ (2 - R)

private lemma complexBoundBad_rejected : ¬ complexBoundArena.Law logarithmBad := by
  intro h
  have hh := h (R := 2) (by norm_num) 0
  change (∫ σ : ℝ in Ioi (2 : ℝ),
    ‖Complex.log (riemannZeta ((σ : ℂ) + ((0 : ℝ) : ℂ) * I))‖) ≤
      Ctail / (-1) * (2 : ℝ) ^ (2 - (2 : ℝ)) at hh
  simp only [div_neg, div_one, sub_self, Real.rpow_zero, mul_one] at hh
  have hi : 0 ≤ ∫ σ : ℝ in Ioi (2 : ℝ),
      ‖Complex.log (riemannZeta ((σ : ℂ) + ((0 : ℝ) : ℂ) * I))‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  linarith [tailCoefficient_pos]

def realBoundArena : Arena where
  signature := realSignature
  Law O := ∀ {R : ℝ} (_ : 2 ≤ R) (t : ℝ),
    (∫ σ : ℝ in Ioi R, |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖|) ≤
      Ctail / O.readout () () 2 * (2 : ℝ) ^ (2 - R)

private lemma realBoundBad_rejected : ¬ realBoundArena.Law logarithmBad := by
  intro h
  have hh := h (R := 2) (by norm_num) 0
  change (∫ σ : ℝ in Ioi (2 : ℝ),
    |Real.log ‖riemannZeta ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)‖|) ≤
      Ctail / (-1) * (2 : ℝ) ^ (2 - (2 : ℝ)) at hh
  simp only [div_neg, div_one, sub_self, Real.rpow_zero, mul_one] at hh
  have hi : 0 ≤ ∫ σ : ℝ in Ioi (2 : ℝ),
      |Real.log ‖riemannZeta ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)‖| :=
    integral_nonneg (fun _ => abs_nonneg _)
  linarith [tailCoefficient_pos]

def truncationArena : Arena where
  signature := realSignature
  Law O := ∀ {R X : ℝ} (_ : 2 ≤ R) (_ : R ≤ X) (t : ℝ),
    |zetaHorizontalLogTail R t -
      (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)| ≤
      Ctail / O.readout () () 2 * (2 : ℝ) ^ (2 - X)

private lemma truncationBad_rejected : ¬ truncationArena.Law logarithmBad := by
  intro h
  have hh := h (R := 2) (X := 2) (by norm_num) le_rfl 0
  change |zetaHorizontalLogTail 2 0 -
    (∫ σ : ℝ in (2 : ℝ)..2, Real.log ‖riemannZeta ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)‖)| ≤
      Ctail / (-1) * (2 : ℝ) ^ (2 - (2 : ℝ)) at hh
  simp only [intervalIntegral.integral_same, sub_zero, div_neg, div_one,
    sub_self, Real.rpow_zero, mul_one] at hh
  linarith [tailCoefficient_pos, abs_nonneg (zetaHorizontalLogTail 2 0)]

def transportArena : Arena where
  signature := imSignature
  Law O := ∀ {R : ℝ} (_ : 2 ≤ R) (u v : ℝ),
    zetaHorizontalLogTail R v - zetaHorizontalLogTail R u =
      ∫ t : ℝ in u..v, O.readout () ()
        (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I)))

def transportBad : Realization imSignature :=
  realize imSignature (fun _ _ _ =>
    zetaHorizontalLogTail 2 1 - zetaHorizontalLogTail 2 0 + 1) (fun e => nomatch e)

private lemma transportBad_rejected : ¬ transportArena.Law transportBad := by
  intro h
  have hh := h (R := 2) (by norm_num) 0 1
  change zetaHorizontalLogTail 2 1 - zetaHorizontalLogTail 2 0 =
    ∫ _t : ℝ in (0 : ℝ)..1,
      zetaHorizontalLogTail 2 1 - zetaHorizontalLogTail 2 0 + 1 at hh
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hh
  linarith

def normEvidence : Registration normArena (type_of% @norm_log_riemannZeta_le_rpow) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨norm_log_riemannZeta_le_rpow, normBad, normBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    normArena.Law complexActual normBad normBad_rejected
  dependence := complexDependence

def complexIntegrableEvidence :
    Registration complexIntegrableArena (type_of% @integrableOn_principal_log_riemannZeta_Ioi) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨integrableOn_principal_log_riemannZeta_Ioi, complexIntegrableBad,
    complexIntegrableBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    complexIntegrableArena.Law complexActual complexIntegrableBad complexIntegrableBad_rejected
  dependence := complexDependence

def realIntegrableEvidence :
    Registration realIntegrableArena (type_of% @integrableOn_log_norm_riemannZeta_Ioi) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨integrableOn_log_norm_riemannZeta_Ioi, realIntegrableBad,
    realIntegrableBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    realIntegrableArena.Law realActual realIntegrableBad realIntegrableBad_rejected
  dependence := realDependence

def complexBoundEvidence :
    Registration complexBoundArena (type_of% @integral_norm_principal_log_riemannZeta_Ioi_le) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨integral_norm_principal_log_riemannZeta_Ioi_le, logarithmBad,
    complexBoundBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    complexBoundArena.Law realActual logarithmBad complexBoundBad_rejected
  dependence := realDependence

def realBoundEvidence :
    Registration realBoundArena (type_of% @integral_abs_log_norm_riemannZeta_Ioi_le) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨integral_abs_log_norm_riemannZeta_Ioi_le, logarithmBad, realBoundBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    realBoundArena.Law realActual logarithmBad realBoundBad_rejected
  dependence := realDependence

def truncationEvidence :
    Registration truncationArena (type_of% @abs_zetaHorizontalLogTail_sub_intervalIntegral_le) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨abs_zetaHorizontalLogTail_sub_intervalIntegral_le, logarithmBad,
    truncationBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    truncationArena.Law realActual logarithmBad truncationBad_rejected
  dependence := realDependence

def transportEvidence :
    Registration transportArena (type_of% @zetaHorizontalLogTail_sub_eq_intervalIntegral) where
  actual := imActual
  bridge := Iff.rfl
  variation := ⟨zetaHorizontalLogTail_sub_eq_intervalIntegral, transportBad, transportBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    transportArena.Law imActual transportBad transportBad_rejected
  dependence := imDependence

def normAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norm_log_riemannZeta_le_rpow) (Realization complexSignature) Unit Unit where
  unitName := `Zeta23.RvM.norm_log_riemannZeta_le_rpow.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.normEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨normArena⟩
  objectArena := .source ⟨normArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normArena ⟨normEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature (fun _ _ z => Complex.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def complexIntegrableAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrableOn_principal_log_riemannZeta_Ioi) (Realization complexSignature) Unit Unit where
  unitName := `Zeta23.RvM.integrableOn_principal_log_riemannZeta_Ioi.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.complexIntegrableEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨complexIntegrableArena⟩
  objectArena := .source ⟨complexIntegrableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source complexIntegrableArena ⟨complexIntegrableEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature (fun _ _ z => Complex.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def realIntegrableAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrableOn_log_norm_riemannZeta_Ioi) (Realization realSignature) Unit Unit where
  unitName := `Zeta23.RvM.integrableOn_log_norm_riemannZeta_Ioi.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.realIntegrableEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨realIntegrableArena⟩
  objectArena := .source ⟨realIntegrableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source realIntegrableArena ⟨realIntegrableEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ z => Real.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def complexBoundAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_norm_principal_log_riemannZeta_Ioi_le) (Realization realSignature) Unit Unit where
  unitName := `Zeta23.RvM.integral_norm_principal_log_riemannZeta_Ioi_le.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.complexBoundEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨complexBoundArena⟩
  objectArena := .source ⟨complexBoundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source complexBoundArena ⟨complexBoundEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ z => Real.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def realBoundAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_abs_log_norm_riemannZeta_Ioi_le) (Realization realSignature) Unit Unit where
  unitName := `Zeta23.RvM.integral_abs_log_norm_riemannZeta_Ioi_le.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.realBoundEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨realBoundArena⟩
  objectArena := .source ⟨realBoundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source realBoundArena ⟨realBoundEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ z => Real.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def truncationAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_zetaHorizontalLogTail_sub_intervalIntegral_le) (Realization realSignature) Unit Unit where
  unitName := `Zeta23.RvM.abs_zetaHorizontalLogTail_sub_intervalIntegral_le.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.truncationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨truncationArena⟩
  objectArena := .source ⟨truncationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source truncationArena ⟨truncationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ z => Real.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def transportAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zetaHorizontalLogTail_sub_eq_intervalIntegral) (Realization imSignature) Unit Unit where
  unitName := `Zeta23.RvM.zetaHorizontalLogTail_sub_eq_intervalIntegral.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.transportEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transportArena ⟨transportEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize imSignature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev reSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def reActual : Realization reSignature :=
  realize reSignature (fun _ _ z => z.re) (fun e => nomatch e)

def reArena : Arena where
  signature := reSignature
  Law O := ∀ {s : ℂ}, 2 ≤ s.re → 0 < O.readout () () (riemannZeta s)

def reBad : Realization reSignature :=
  realize reSignature (fun _ _ _ => -1) (fun e => nomatch e)

private lemma reBad_rejected : ¬ reArena.Law reBad := by
  intro h
  have hh := h (s := 2) (by norm_num)
  change (0 : ℝ) < -1 at hh
  linarith

private lemma reDependence : ObservationalDependence reSignature reActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def reEvidence : Registration reArena (type_of% @re_zeta_pos_of_two_le_re) where
  actual := reActual
  bridge := Iff.rfl
  variation := ⟨re_zeta_pos_of_two_le_re, reBad, reBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    reArena.Law reActual reBad reBad_rejected
  dependence := reDependence

def reAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@re_zeta_pos_of_two_le_re) (Realization reSignature) Unit Unit where
  unitName := `Zeta23.RvM.re_zeta_pos_of_two_le_re.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail.reEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨reArena⟩
  objectArena := .source ⟨reArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reArena ⟨reEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize reSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalLogTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaRvm.HorizontalLogTail
