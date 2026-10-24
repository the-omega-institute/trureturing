import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
open _root_.D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
open LeanInformationAudit
open scoped ENNReal

noncomputable section
namespace Reg.D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk

abbrev fullSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ≥0∞)

def fullActual : Realization fullSignature :=
  realize fullSignature (fun _ p H => minimaxRisk p.1 p.2.1 H p.2.2 full)
    (fun e => nomatch e)

def fullTop : Realization fullSignature :=
  realize fullSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

def fullArena : Arena where
  signature := fullSignature
  Law r := ∀ (m ε H s : ℝ) (_hm : 0 < m) (_hε : 0 < ε) (_hH : 0 < H),
    r.readout () ⟨m, ε, s⟩ H =
      ENNReal.ofReal (min H (envelope (2 * ε / m) (H + |s|)) / 2)

private theorem fullPositive : fullArena.Law fullActual := @full_risk

private theorem fullNegative : ¬ fullArena.Law fullTop := by
  intro h
  have hh := h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  change (⊤ : ℝ≥0∞) = ENNReal.ofReal _ at hh
  exact ENNReal.ofReal_ne_top hh.symm

private theorem fullDependence : ObservationalDependence fullSignature fullActual := by
  intro i
  refine ⟨⟨1, 1, 0⟩, 1 / 100, 1, ?_⟩
  intro he
  change minimaxRisk 1 1 (1 / 100) 0 full = minimaxRisk 1 1 1 0 full at he
  have hsmall := (raw_minimax 1 1 (1 / 100) 0 (by norm_num) full).2.2.1
  have hbig := full_risk 1 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num [envelope] at hbig
  rw [he, hbig] at hsmall
  norm_num at hsmall

def fullEvidence : Registration fullArena (fullArena.Law fullActual) where
  actual := fullActual
  bridge := Iff.rfl
  variation := ⟨fullPositive, fullTop, fullNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    fullArena.Law fullActual fullTop fullNegative
  dependence := fullDependence

abbrev deletionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Index)
    (fun _ => ℝ) (fun _ => ℝ≥0∞)

def deletionActual : Realization deletionSignature :=
  realize deletionSignature
    (fun _ p H => minimaxRisk p.1 p.2.1 H p.2.2.1 (full.erase p.2.2.2))
    (fun e => nomatch e)

def deletionZero : Realization deletionSignature :=
  realize deletionSignature (fun _ _ _ => 0) (fun e => nomatch e)

def deletionArena : Arena where
  signature := deletionSignature
  Law r := ∀ (m ε H s : ℝ) (_hm : 0 < m) (_hε : 0 < ε) (p : Index),
    ENNReal.ofReal (min H ((2 * ε / m) * (H + |s + deletionSlope p - 10|) /
      (deletionRange p + 2 * (2 * ε / m))) / 2) ≤ r.readout () ⟨m, ε, s, p⟩ H

private theorem deletionPositive : deletionArena.Law deletionActual := @deletion_lower

private def i0 : Index := ⟨0, by norm_num [positions]⟩

private theorem deletionNegative : ¬ deletionArena.Law deletionZero := by
  intro h
  have hh := h 1 1 1 0 (by norm_num) (by norm_num) i0
  norm_num [deletionZero, realize, deletionSlope, deletionRange, i0] at hh

private theorem deletionDependence :
    ObservationalDependence deletionSignature deletionActual := by
  intro i
  refine ⟨⟨1, 1, 0, i0⟩, 1 / 100, 1, ?_⟩
  intro he
  change minimaxRisk 1 1 (1 / 100) 0 (full.erase i0) =
    minimaxRisk 1 1 1 0 (full.erase i0) at he
  have hsmall := (raw_minimax 1 1 (1 / 100) 0 (by norm_num) (full.erase i0)).2.2.1
  have hbig := deletion_lower 1 1 1 0 (by norm_num) (by norm_num) i0
  norm_num [deletionSlope, deletionRange, i0] at hbig
  rw [he] at hsmall
  have hh := hbig.trans hsmall
  norm_num at hh

def deletionEvidence : Registration deletionArena (deletionArena.Law deletionActual) where
  actual := deletionActual
  bridge := Iff.rfl
  variation := ⟨deletionPositive, deletionZero, deletionNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    deletionArena.Law deletionActual deletionZero deletionNegative
  dependence := deletionDependence

def fullRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_risk)
    (type_of% (realize fullSignature
      (fun _ p H => minimaxRisk p.1 p.2.1 H p.2.2 full) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk.full_risk.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk.fullEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨fullArena⟩
  objectArena := .source ⟨fullArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullArena ⟨fullEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fullSignature
    (fun _ p H => minimaxRisk p.1 p.2.1 H p.2.2 full) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def deletionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deletion_lower)
    (type_of% (realize deletionSignature
      (fun _ p H => minimaxRisk p.1 p.2.1 H p.2.2.1 (full.erase p.2.2.2))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk.deletion_lower.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk.deletionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨deletionArena⟩
  objectArena := .source ⟨deletionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deletionArena ⟨deletionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deletionSignature
    (fun _ p H => minimaxRisk p.1 p.2.1 H p.2.2.1 (full.erase p.2.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
    definition := none
    coordinates := #[0, 1, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms fullEvidence
#print axioms deletionEvidence
#print axioms fullRegistration
#print axioms deletionRegistration

abbrev calibrationSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def calibrationActual : Realization calibrationSignature :=
  realize calibrationSignature
    (fun _ p d => 2 * (p.1 + |p.2.2.2.2.2.1 - p.2.2.2.2.2.2|) * d)
    (fun e => nomatch e)

def calibrationBad : Realization calibrationSignature :=
  realize calibrationSignature (fun _ _ _ => 1) (fun e => nomatch e)

def calibrationArena : Arena where
  signature := calibrationSignature
  Law r := ∀ (m H s u v A A' : ℝ)
    (_hu : u ∈ prior H s) (_hv : v ∈ prior H s) (_huv : u ≤ v)
    (_hA : m ≤ A) (_hA' : m ≤ A'),
    let U := A - A'
    let W := 10 * U + 2 * (A * u - A' * v)
    r.readout () ⟨m, H, s, u, v, A, A'⟩ (v - u) ≤
      (H + |s|) * |U| + |W|

private theorem calibrationPositive : calibrationArena.Law calibrationActual := @calibration_bound

private theorem calibrationNegative : ¬ calibrationArena.Law calibrationBad := by
  intro h
  have hh := h 0 0 0 (-5) (-5) 0 0 (by norm_num [prior]) (by norm_num [prior])
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [calibrationBad, realize] at hh

private theorem calibrationDependence :
    ObservationalDependence calibrationSignature calibrationActual := by
  intro i
  refine ⟨⟨1, 2, 0, -5, -4, 1, 1⟩, 0, 1, ?_⟩
  norm_num [calibrationActual, realize]

def calibrationEvidence :
    Registration calibrationArena (calibrationArena.Law calibrationActual) where
  actual := calibrationActual
  bridge := Iff.rfl
  variation := ⟨calibrationPositive, calibrationBad, calibrationNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    calibrationArena.Law calibrationActual calibrationBad calibrationNegative
  dependence := calibrationDependence

def calibrationRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@calibration_bound)
    (type_of% (realize calibrationSignature
      (fun _ p d => 2 * (p.1 + |p.2.2.2.2.2.1 - p.2.2.2.2.2.2|) * d)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk.calibration_bound.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk.calibrationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨calibrationArena⟩
  objectArena := .source ⟨calibrationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source calibrationArena ⟨calibrationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize calibrationSignature
    (fun _ p d => 2 * (p.1 + |p.2.2.2.2.2.1 - p.2.2.2.2.2.2|) * d)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms calibrationEvidence
#print axioms calibrationRegistration

end Reg.D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
