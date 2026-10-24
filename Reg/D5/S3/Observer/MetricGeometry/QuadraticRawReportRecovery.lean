import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
open LeanInformationAudit Set
open scoped ENNReal

noncomputable section
namespace Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery

private def i0 : Index := ⟨0, by norm_num [positions]⟩
private def i1 : Index := ⟨1, by norm_num [positions]⟩
private def i2 : Index := ⟨2, by norm_num [positions]⟩
private def three : Design := {i0, i1, i2}


abbrev rawSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Design (fun _ => World) Reports

def rawActual : Realization rawSignature :=
  realize rawSignature (fun _ J w => observe J w) (fun e => nomatch e)

def rawRejected : Realization rawSignature :=
  realize rawSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

private theorem rawDependence : ObservationalDependence rawSignature rawActual := by
  intro i
  refine ⟨{i0}, ⟨0, 1, 0, fun _ => 0⟩, ⟨0, 1, 1, fun _ => 0⟩, ?_⟩
  intro he
  have hh := congrFun he ⟨i0, by simp⟩
  norm_num [rawActual, realize, observe, signature, i0] at hh

def compatibleArena : Arena where
  signature := rawSignature
  Law r := ∀ (m ε H s : ℝ) (_hε : 0 ≤ ε) (J : Design) (y : Reports J) (t : ℝ),
    (∃ w : World, Legal m ε H s w ∧ w.tau = t ∧ r.readout () J w = y) ↔
      t ∈ prior H s ∧ ∃ A B : ℝ, m ≤ A ∧
        ∀ i : J, |y i - signature t A B i.val| ≤ ε

private theorem compatiblePositive : compatibleArena.Law rawActual := @compatible_iff

private theorem compatibleNegative : ¬ compatibleArena.Law rawRejected := by
  intro h
  have hh := (h 1 0 1 10 (by norm_num) {i0} (fun _ => 1) 0).2
    ⟨by norm_num [prior], 1, 1, le_rfl, by
      intro i
      have hi : i.val = i0 := Finset.mem_singleton.mp i.property
      simp [hi, signature, i0]⟩
  obtain ⟨w, _, _, hy⟩ := hh
  have hz := congrFun hy ⟨i0, by simp⟩
  norm_num [rawRejected, realize] at hz

def compatibleEvidence : Registration compatibleArena (compatibleArena.Law rawActual) where
  actual := rawActual
  bridge := Iff.rfl
  variation := ⟨compatiblePositive, rawRejected, compatibleNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    compatibleArena.Law rawActual rawRejected compatibleNegative
  dependence := rawDependence

def commonArena : Arena where
  signature := rawSignature
  Law r := ∀ (m ε H s : ℝ) (_hε : 0 ≤ ε) (J : Design) (u v : ℝ),
    (∃ w w' : World, Legal m ε H s w ∧ Legal m ε H s w' ∧
      w.tau = u ∧ w'.tau = v ∧ r.readout () J w = observe J w') ↔
      u ∈ prior H s ∧ v ∈ prior H s ∧ PairCompatible m ε J u v

private theorem commonPositive : commonArena.Law rawActual := @common_report_iff

private theorem commonNegative : ¬ commonArena.Law rawRejected := by
  intro h
  have hh := (h 1 0 1 10 (by norm_num) three 0 0).2
    ⟨by norm_num [prior], by norm_num [prior], 1, 1, 0, 0, le_rfl, le_rfl, by simp⟩
  obtain ⟨w, w', hw, hw', _, ht, he⟩ := hh
  have hz0 := hw'.2.2 i0
  have hz1 := hw'.2.2 i1
  have h0 := congrFun he ⟨i0, by simp [three]⟩
  have h1 := congrFun he ⟨i1, by simp [three]⟩
  have hn0 : w'.noise i0 = 0 := abs_nonpos_iff.mp hz0
  have hn1 : w'.noise i1 = 0 := abs_nonpos_iff.mp hz1
  norm_num [rawRejected, realize, observe, signature, ht, hn0, hn1, i0, i1] at h0 h1
  change 0 = w'.zero + w'.noise i0 at h0
  change 0 = w'.gain + w'.zero + w'.noise i1 at h1
  rw [hn0] at h0
  rw [hn1] at h1
  linarith [hw'.2.1]

def commonEvidence : Registration commonArena (commonArena.Law rawActual) where
  actual := rawActual
  bridge := Iff.rfl
  variation := ⟨commonPositive, rawRejected, commonNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    commonArena.Law rawActual rawRejected commonNegative
  dependence := rawDependence

abbrev calibrationSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ)
    (fun _ => Index) (fun _ => ℝ)

def calibrationActual : Realization calibrationSignature :=
  realize calibrationSignature (fun _ p i => signature p.1 p.2.1 p.2.2 i)
    (fun e => nomatch e)

def calibrationRejected : Realization calibrationSignature :=
  realize calibrationSignature (fun _ _ _ => 0) (fun e => nomatch e)

def stripsArena : Arena where
  signature := calibrationSignature
  Law r := ∀ (m ε : ℝ) (J : Design) (u v : ℝ),
    (∃ A A' B B' : ℝ, m ≤ A ∧ m ≤ A' ∧ ∀ i ∈ J,
      |r.readout () ⟨u, A, B⟩ i - signature v A' B' i| ≤ 2 * ε) ↔
      ∃ A A' : ℝ, m ≤ A ∧ m ≤ A' ∧ Strips ε J (A - A') (2 * (A * u - A' * v))

private theorem stripsPositive : stripsArena.Law calibrationActual := @pairCompatible_iff_strips

private theorem stripsNegative : ¬ stripsArena.Law calibrationRejected := by
  intro h
  have hh := (h 1 0 three 0 0).2 ⟨1, 1, le_rfl, le_rfl, by
    intro i hi j hj
    simp⟩
  obtain ⟨A, A', B, B', hA, hA', hd⟩ := hh
  have h0 := hd i0 (by simp [three])
  have h1 := hd i1 (by simp [three])
  norm_num [calibrationRejected, realize, signature, i0, i1] at h0 h1
  linarith

private theorem calibrationDependence :
    ObservationalDependence calibrationSignature calibrationActual := by
  intro i
  refine ⟨⟨0, 1, 0⟩, i0, i1, ?_⟩
  norm_num [calibrationActual, realize, signature, i0, i1]

def stripsEvidence : Registration stripsArena (stripsArena.Law calibrationActual) where
  actual := calibrationActual
  bridge := Iff.rfl
  variation := ⟨stripsPositive, calibrationRejected, stripsNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    stripsArena.Law calibrationActual calibrationRejected stripsNegative
  dependence := calibrationDependence

abbrev riskSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ)
    (fun _ => Design) (fun _ => ℝ≥0∞)

def riskActual : Realization riskSignature :=
  realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J)
    (fun e => nomatch e)

def riskTop : Realization riskSignature :=
  realize riskSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

def riskZero : Realization riskSignature :=
  realize riskSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem zero_noise_identifies (u v : ℝ) (hp : PairCompatible 1 0 three u v) : u = v := by
  obtain ⟨A, A', B, B', hA, hA', hd⟩ := hp
  have h0 := hd i0 (by simp [three])
  have h1 := hd i1 (by simp [three])
  have h2 := hd i2 (by simp [three])
  norm_num [signature, i0, i1, i2] at h0 h1 h2
  have hAA : A = A' := by nlinarith
  subst A'
  have hprod : A * (u - v) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (by linarith))

private theorem three_zero_risk (H s : ℝ) : minimaxRisk 1 0 H s three = 0 := by
  rw [(raw_minimax 1 0 H s (by norm_num) three).1]
  apply le_antisymm ?_ bot_le
  refine iSup_le fun u => iSup_le fun v => iSup_le fun hu => iSup_le fun hv =>
    iSup_le fun hp => ?_
  rw [zero_noise_identifies u v hp]
  simp

private theorem riskDependence : ObservationalDependence riskSignature riskActual := by
  intro i
  refine ⟨⟨1, 0, 1, 0⟩, ∅, three, ?_⟩
  change minimaxRisk 1 0 1 0 ∅ ≠ minimaxRisk 1 0 1 0 three
  rw [three_zero_risk]
  have hp := few_reports_floor 1 0 1 0 (by norm_num) (by norm_num) (by norm_num) ∅ (by simp)
  intro he
  rw [he] at hp
  norm_num at hp

def recoveryArena : Arena where
  signature := riskSignature
  Law r := ∀ (m ε H s : ℝ) (_hε : 0 ≤ ε) (J : Design),
    r.readout () ⟨m, ε, H, s⟩ J = ambiguityRadius m ε H s J ∧
    risk m ε H s J (midpointRule m ε H s J) = ambiguityRadius m ε H s J ∧
    minimaxRisk m ε H s J ≤ ENNReal.ofReal (H / 2) ∧
    minimaxRisk m ε H s J < ⊤

private theorem recoveryPositive : recoveryArena.Law riskActual := @raw_minimax

private theorem recoveryNegative : ¬ recoveryArena.Law riskTop := by
  intro h
  have hh := (h 1 0 1 0 (by norm_num) ∅).1
  have hb := (raw_minimax 1 0 1 0 (by norm_num) ∅).2.2.1
  rw [(raw_minimax 1 0 1 0 (by norm_num) ∅).1, ← hh] at hb
  norm_num [riskTop, realize] at hb

def recoveryEvidence : Registration recoveryArena (recoveryArena.Law riskActual) where
  actual := riskActual
  bridge := Iff.rfl
  variation := ⟨recoveryPositive, riskTop, recoveryNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    recoveryArena.Law riskActual riskTop recoveryNegative
  dependence := riskDependence

def projectionArena : Arena where
  signature := riskSignature
  Law r := ∀ (m ε H s : ℝ) (J K : Design) (_hJK : J ⊆ K),
    r.readout () ⟨m, ε, H, s⟩ K ≤ minimaxRisk m ε H s J

private theorem projectionPositive : projectionArena.Law riskActual := @projection_monotone

private theorem projectionNegative : ¬ projectionArena.Law riskTop := by
  intro h
  have hh := h 1 0 1 0 ∅ ∅ (by simp)
  have hb := (raw_minimax 1 0 1 0 (by norm_num) ∅).2.2.1
  exact (not_le_of_gt (ENNReal.ofReal_lt_top)) (le_trans hh hb)

def projectionEvidence : Registration projectionArena (projectionArena.Law riskActual) where
  actual := riskActual
  bridge := Iff.rfl
  variation := ⟨projectionPositive, riskTop, projectionNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    projectionArena.Law riskActual riskTop projectionNegative
  dependence := riskDependence

def floorArena : Arena where
  signature := riskSignature
  Law r := ∀ (m ε H s : ℝ) (_hm : 0 < m) (_hε : 0 ≤ ε)
    (_hH : 0 < H) (J : Design) (_hJ : J.card ≤ 2),
    ENNReal.ofReal (H / 4) ≤ r.readout () ⟨m, ε, H, s⟩ J

private theorem floorPositive : floorArena.Law riskActual := @few_reports_floor

private theorem floorNegative : ¬ floorArena.Law riskZero := by
  intro h
  have hh := h 1 0 1 0 (by norm_num) (by norm_num) (by norm_num) ∅ (by simp)
  norm_num [riskZero, realize] at hh

def floorEvidence : Registration floorArena (floorArena.Law riskActual) where
  actual := riskActual
  bridge := Iff.rfl
  variation := ⟨floorPositive, riskZero, floorNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    floorArena.Law riskActual riskZero floorNegative
  dependence := riskDependence


def compatibleRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compatible_iff)
    (type_of% (realize rawSignature (fun _ J w => observe J w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.compatible_iff.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.compatibleEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨compatibleArena⟩
  objectArena := .source ⟨compatibleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compatibleArena ⟨compatibleEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rawSignature (fun _ J w => observe J w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms compatibleEvidence
#print axioms compatibleRegistration

def commonRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_report_iff)
    (type_of% (realize rawSignature (fun _ J w => observe J w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.common_report_iff.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.commonEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨commonArena⟩
  objectArena := .source ⟨commonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source commonArena ⟨commonEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rawSignature (fun _ J w => observe J w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms commonEvidence
#print axioms commonRegistration

def stripsRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairCompatible_iff_strips)
    (type_of% (realize calibrationSignature (fun _ p i => signature p.1 p.2.1 p.2.2 i) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.pairCompatible_iff_strips.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.stripsEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨stripsArena⟩
  objectArena := .source ⟨stripsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stripsArena ⟨stripsEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize calibrationSignature (fun _ p i => signature p.1 p.2.1 p.2.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
    definition := none
    coordinates := #[3, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms stripsEvidence
#print axioms stripsRegistration

def recoveryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@raw_minimax)
    (type_of% (realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.raw_minimax.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.recoveryEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨recoveryArena⟩
  objectArena := .source ⟨recoveryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recoveryArena ⟨recoveryEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms recoveryEvidence
#print axioms recoveryRegistration

def projectionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@projection_monotone)
    (type_of% (realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.projection_monotone.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.projectionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨projectionArena⟩
  objectArena := .source ⟨projectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionArena ⟨projectionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms projectionEvidence
#print axioms projectionRegistration

def floorRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@few_reports_floor)
    (type_of% (realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.few_reports_floor.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery.floorEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨floorArena⟩
  objectArena := .source ⟨floorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source floorArena ⟨floorEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize riskSignature (fun _ p J => minimaxRisk p.1 p.2.1 p.2.2.1 p.2.2.2 J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms floorEvidence
#print axioms floorRegistration

end Reg.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
