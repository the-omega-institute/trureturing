import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.WallisRemainder.Measure
import Reg.D5.S3.Analytic.WallisRemainder.Laplace
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.WallisRemainder.Measure
open _root_.D5.S3.Analytic.WallisRemainder.Defs
open _root_.D5.S3.Analytic.WallisRemainder.Measure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev measureSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Measure ℝ) (fun _ => Bool)

def measureRejected : Realization measureSignature :=
  realize measureSignature (fun _ _ _ => false) (fun e => nomatch e)

def integrable_P_idActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v) μ)) (fun e => nomatch e)

abbrev integrable_P_idArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem integrable_P_idRejected : ¬ integrable_P_idArena.Law measureRejected := by
  simp [integrable_P_idArena, measureRejected, realize]

private theorem integrable_P_idDependence : ObservationalDependence measureSignature integrable_P_idActual := by
  intro i
  have hn : ¬ Integrable (fun v : ℝ => v) (volume : Measure ℝ) := by
    intro h
    have hi := h.integrableOn (s := Ioi (1 : ℝ))
    have hr : IntegrableOn (fun v : ℝ => v ^ (1 : ℝ)) (Ioi 1) := by
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_one] using hi
    have hh := (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hr
    norm_num at hh
  refine ⟨(), 0, volume, ?_⟩
  simp [integrable_P_idActual, realize, hn]

def integrable_P_idFamily : Registration integrable_P_idArena (type_of% @integrable_P_id) where
  actual := integrable_P_idActual
  bridge := by simp [integrable_P_idArena, integrable_P_idActual, realize]
  variation := ⟨by simpa [integrable_P_idActual, realize] using integrable_P_id, measureRejected, integrable_P_idRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrable_P_idArena.Law integrable_P_idActual measureRejected integrable_P_idRejected
  dependence := integrable_P_idDependence

def integrable_P_idAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_P_id) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_P_idUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_P_idFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrable_P_idArena⟩
  objectArena := .source ⟨integrable_P_idArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrable_P_idArena ⟨integrable_P_idFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v) μ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integral_P_idActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ∂μ) = (1 / 24 : ℝ))) (fun e => nomatch e)

abbrev integral_P_idArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem integral_P_idRejected : ¬ integral_P_idArena.Law measureRejected := by
  simp [integral_P_idArena, measureRejected, realize]

private theorem integral_P_idDependence : ObservationalDependence measureSignature integral_P_idActual := by
  intro i
  refine ⟨(), P, 0, ?_⟩
  norm_num [integral_P_idActual, realize, integral_P_id]

def integral_P_idFamily : Registration integral_P_idArena (type_of% @integral_P_id) where
  actual := integral_P_idActual
  bridge := by simp [integral_P_idArena, integral_P_idActual, realize]
  variation := ⟨by simpa [integral_P_idActual, realize] using integral_P_id, measureRejected, integral_P_idRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integral_P_idArena.Law integral_P_idActual measureRejected integral_P_idRejected
  dependence := integral_P_idDependence

def integral_P_idAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_P_id) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_P_idUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_P_idFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integral_P_idArena⟩
  objectArena := .source ⟨integral_P_idArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integral_P_idArena ⟨integral_P_idFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ∂μ) = (1 / 24 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integrable_P_sqActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v ^ 2) μ)) (fun e => nomatch e)

abbrev integrable_P_sqArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem integrable_P_sqRejected : ¬ integrable_P_sqArena.Law measureRejected := by
  simp [integrable_P_sqArena, measureRejected, realize]

private theorem integrable_P_sqDependence : ObservationalDependence measureSignature integrable_P_sqActual := by
  intro i
  have hn : ¬ Integrable (fun v : ℝ => v ^ 2) (volume : Measure ℝ) := by
    intro h
    have hi := h.integrableOn (s := Ioi (1 : ℝ))
    have hr : IntegrableOn (fun v : ℝ => v ^ (2 : ℝ)) (Ioi 1) := by
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using hi
    have hh := (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hr
    norm_num at hh
  refine ⟨(), 0, volume, ?_⟩
  simp [integrable_P_sqActual, realize, hn]

def integrable_P_sqFamily : Registration integrable_P_sqArena (type_of% @integrable_P_sq) where
  actual := integrable_P_sqActual
  bridge := by simp [integrable_P_sqArena, integrable_P_sqActual, realize]
  variation := ⟨by simpa [integrable_P_sqActual, realize] using integrable_P_sq, measureRejected, integrable_P_sqRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrable_P_sqArena.Law integrable_P_sqActual measureRejected integrable_P_sqRejected
  dependence := integrable_P_sqDependence

def integrable_P_sqAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_P_sq) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_P_sqUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_P_sqFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrable_P_sqArena⟩
  objectArena := .source ⟨integrable_P_sqArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrable_P_sqArena ⟨integrable_P_sqFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v ^ 2) μ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integral_P_sqActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ^ 2 ∂μ) = (1 / 80 : ℝ))) (fun e => nomatch e)

abbrev integral_P_sqArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem integral_P_sqRejected : ¬ integral_P_sqArena.Law measureRejected := by
  simp [integral_P_sqArena, measureRejected, realize]

private theorem integral_P_sqDependence : ObservationalDependence measureSignature integral_P_sqActual := by
  intro i
  refine ⟨(), P, 0, ?_⟩
  norm_num [integral_P_sqActual, realize, integral_P_sq]

def integral_P_sqFamily : Registration integral_P_sqArena (type_of% @integral_P_sq) where
  actual := integral_P_sqActual
  bridge := by simp [integral_P_sqArena, integral_P_sqActual, realize]
  variation := ⟨by simpa [integral_P_sqActual, realize] using integral_P_sq, measureRejected, integral_P_sqRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integral_P_sqArena.Law integral_P_sqActual measureRejected integral_P_sqRejected
  dependence := integral_P_sqDependence

def integral_P_sqAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_P_sq) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_P_sqUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_P_sqFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integral_P_sqArena⟩
  objectArena := .source ⟨integral_P_sqArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integral_P_sqArena ⟨integral_P_sqFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ^ 2 ∂μ) = (1 / 80 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integrable_P_cubeActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v ^ 3) μ)) (fun e => nomatch e)

abbrev integrable_P_cubeArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem integrable_P_cubeRejected : ¬ integrable_P_cubeArena.Law measureRejected := by
  simp [integrable_P_cubeArena, measureRejected, realize]

private theorem integrable_P_cubeDependence : ObservationalDependence measureSignature integrable_P_cubeActual := by
  intro i
  have hn : ¬ Integrable (fun v : ℝ => v ^ 3) (volume : Measure ℝ) := by
    intro h
    have hi := h.integrableOn (s := Ioi (1 : ℝ))
    have hr : IntegrableOn (fun v : ℝ => v ^ (3 : ℝ)) (Ioi 1) := by
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using hi
    have hh := (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hr
    norm_num at hh
  refine ⟨(), 0, volume, ?_⟩
  simp [integrable_P_cubeActual, realize, hn]

def integrable_P_cubeFamily : Registration integrable_P_cubeArena (type_of% @integrable_P_cube) where
  actual := integrable_P_cubeActual
  bridge := by simp [integrable_P_cubeArena, integrable_P_cubeActual, realize]
  variation := ⟨by simpa [integrable_P_cubeActual, realize] using integrable_P_cube, measureRejected, integrable_P_cubeRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrable_P_cubeArena.Law integrable_P_cubeActual measureRejected integrable_P_cubeRejected
  dependence := integrable_P_cubeDependence

def integrable_P_cubeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_P_cube) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_P_cubeUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_P_cubeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrable_P_cubeArena⟩
  objectArena := .source ⟨integrable_P_cubeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrable_P_cubeArena ⟨integrable_P_cubeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v ^ 3) μ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integral_P_cubeActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ^ 3 ∂μ) = (17 / 1792 : ℝ))) (fun e => nomatch e)

abbrev integral_P_cubeArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem integral_P_cubeRejected : ¬ integral_P_cubeArena.Law measureRejected := by
  simp [integral_P_cubeArena, measureRejected, realize]

private theorem integral_P_cubeDependence : ObservationalDependence measureSignature integral_P_cubeActual := by
  intro i
  refine ⟨(), P, 0, ?_⟩
  norm_num [integral_P_cubeActual, realize, integral_P_cube]

def integral_P_cubeFamily : Registration integral_P_cubeArena (type_of% @integral_P_cube) where
  actual := integral_P_cubeActual
  bridge := by simp [integral_P_cubeArena, integral_P_cubeActual, realize]
  variation := ⟨by simpa [integral_P_cubeActual, realize] using integral_P_cube, measureRejected, integral_P_cubeRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integral_P_cubeArena.Law integral_P_cubeActual measureRejected integral_P_cubeRejected
  dependence := integral_P_cubeDependence

def integral_P_cubeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_P_cube) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_P_cubeUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_P_cubeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integral_P_cubeArena⟩
  objectArena := .source ⟨integral_P_cubeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integral_P_cubeArena ⟨integral_P_cubeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ^ 3 ∂μ) = (17 / 1792 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def P_posActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∀ᵐ v ∂μ, (0 : ℝ) < v))) (fun e => nomatch e)

abbrev P_posArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem P_posRejected : ¬ P_posArena.Law measureRejected := by
  simp [P_posArena, measureRejected, realize]

private theorem P_posDependence : ObservationalDependence measureSignature P_posActual := by
  intro i
  refine ⟨(), 0, Measure.dirac (0 : ℝ), ?_⟩
  simp [P_posActual, realize]

def P_posFamily : Registration P_posArena (type_of% @P_pos) where
  actual := P_posActual
  bridge := by simp [P_posArena, P_posActual, realize]
  variation := ⟨by simpa [P_posActual, realize] using P_pos, measureRejected, P_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    P_posArena.Law P_posActual measureRejected P_posRejected
  dependence := P_posDependence

def P_posAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@P_pos) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.P_posUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.P_posFamily
  realizationSource := none
  generated := false
  arena := .source ⟨P_posArena⟩
  objectArena := .source ⟨P_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source P_posArena ⟨P_posFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∀ᵐ v ∂μ, (0 : ℝ) < v))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def variance_PActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (ProbabilityTheory.variance (fun v : ℝ => v) μ = (31 / 2880 : ℝ))) (fun e => nomatch e)

abbrev variance_PArena : Arena where
  signature := measureSignature
  Law R := R.readout () () P = true

private theorem variance_PRejected : ¬ variance_PArena.Law measureRejected := by
  simp [variance_PArena, measureRejected, realize]

private theorem variance_PDependence : ObservationalDependence measureSignature variance_PActual := by
  intro i
  refine ⟨(), P, 0, ?_⟩
  norm_num [variance_PActual, realize, variance_P]

def variance_PFamily : Registration variance_PArena (type_of% @variance_P) where
  actual := variance_PActual
  bridge := by simp [variance_PArena, variance_PActual, realize]
  variation := ⟨by simpa [variance_PActual, realize] using variance_P, measureRejected, variance_PRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    variance_PArena.Law variance_PActual measureRejected variance_PRejected
  dependence := variance_PDependence

def variance_PAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@variance_P) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.variance_PUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.variance_PFamily
  realizationSource := none
  generated := false
  arena := .source ⟨variance_PArena⟩
  objectArena := .source ⟨variance_PArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source variance_PArena ⟨variance_PFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (ProbabilityTheory.variance (fun v : ℝ => v) μ = (31 / 2880 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integrable_Q_idActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v) μ)) (fun e => nomatch e)

abbrev integrable_Q_idArena : Arena where
  signature := measureSignature
  Law R := R.readout () () Q = true

private theorem integrable_Q_idRejected : ¬ integrable_Q_idArena.Law measureRejected := by
  simp [integrable_Q_idArena, measureRejected, realize]

private theorem integrable_Q_idDependence : ObservationalDependence measureSignature integrable_Q_idActual := by
  intro i
  have hn : ¬ Integrable (fun v : ℝ => v) (volume : Measure ℝ) := by
    intro h
    have hi := h.integrableOn (s := Ioi (1 : ℝ))
    have hr : IntegrableOn (fun v : ℝ => v ^ (1 : ℝ)) (Ioi 1) := by
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_one] using hi
    have hh := (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hr
    norm_num at hh
  refine ⟨(), 0, volume, ?_⟩
  simp [integrable_Q_idActual, realize, hn]

def integrable_Q_idFamily : Registration integrable_Q_idArena (type_of% @integrable_Q_id) where
  actual := integrable_Q_idActual
  bridge := by simp [integrable_Q_idArena, integrable_Q_idActual, realize]
  variation := ⟨by simpa [integrable_Q_idActual, realize] using integrable_Q_id, measureRejected, integrable_Q_idRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrable_Q_idArena.Law integrable_Q_idActual measureRejected integrable_Q_idRejected
  dependence := integrable_Q_idDependence

def integrable_Q_idAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_Q_id) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_Q_idUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_Q_idFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrable_Q_idArena⟩
  objectArena := .source ⟨integrable_Q_idArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrable_Q_idArena ⟨integrable_Q_idFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v) μ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integral_Q_idActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ∂μ) = (3 / 10 : ℝ))) (fun e => nomatch e)

abbrev integral_Q_idArena : Arena where
  signature := measureSignature
  Law R := R.readout () () Q = true

private theorem integral_Q_idRejected : ¬ integral_Q_idArena.Law measureRejected := by
  simp [integral_Q_idArena, measureRejected, realize]

private theorem integral_Q_idDependence : ObservationalDependence measureSignature integral_Q_idActual := by
  intro i
  refine ⟨(), Q, 0, ?_⟩
  norm_num [integral_Q_idActual, realize, integral_Q_id]

def integral_Q_idFamily : Registration integral_Q_idArena (type_of% @integral_Q_id) where
  actual := integral_Q_idActual
  bridge := by simp [integral_Q_idArena, integral_Q_idActual, realize]
  variation := ⟨by simpa [integral_Q_idActual, realize] using integral_Q_id, measureRejected, integral_Q_idRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integral_Q_idArena.Law integral_Q_idActual measureRejected integral_Q_idRejected
  dependence := integral_Q_idDependence

def integral_Q_idAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_Q_id) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_Q_idUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_Q_idFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integral_Q_idArena⟩
  objectArena := .source ⟨integral_Q_idArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integral_Q_idArena ⟨integral_Q_idFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ∂μ) = (3 / 10 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integrable_Q_sqActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v ^ 2) μ)) (fun e => nomatch e)

abbrev integrable_Q_sqArena : Arena where
  signature := measureSignature
  Law R := R.readout () () Q = true

private theorem integrable_Q_sqRejected : ¬ integrable_Q_sqArena.Law measureRejected := by
  simp [integrable_Q_sqArena, measureRejected, realize]

private theorem integrable_Q_sqDependence : ObservationalDependence measureSignature integrable_Q_sqActual := by
  intro i
  have hn : ¬ Integrable (fun v : ℝ => v ^ 2) (volume : Measure ℝ) := by
    intro h
    have hi := h.integrableOn (s := Ioi (1 : ℝ))
    have hr : IntegrableOn (fun v : ℝ => v ^ (2 : ℝ)) (Ioi 1) := by
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using hi
    have hh := (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hr
    norm_num at hh
  refine ⟨(), 0, volume, ?_⟩
  simp [integrable_Q_sqActual, realize, hn]

def integrable_Q_sqFamily : Registration integrable_Q_sqArena (type_of% @integrable_Q_sq) where
  actual := integrable_Q_sqActual
  bridge := by simp [integrable_Q_sqArena, integrable_Q_sqActual, realize]
  variation := ⟨by simpa [integrable_Q_sqActual, realize] using integrable_Q_sq, measureRejected, integrable_Q_sqRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrable_Q_sqArena.Law integrable_Q_sqActual measureRejected integrable_Q_sqRejected
  dependence := integrable_Q_sqDependence

def integrable_Q_sqAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_Q_sq) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_Q_sqUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integrable_Q_sqFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrable_Q_sqArena⟩
  objectArena := .source ⟨integrable_Q_sqArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrable_Q_sqArena ⟨integrable_Q_sqFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (Integrable (fun v : ℝ => v ^ 2) μ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integral_Q_sqActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ^ 2 ∂μ) = (51 / 224 : ℝ))) (fun e => nomatch e)

abbrev integral_Q_sqArena : Arena where
  signature := measureSignature
  Law R := R.readout () () Q = true

private theorem integral_Q_sqRejected : ¬ integral_Q_sqArena.Law measureRejected := by
  simp [integral_Q_sqArena, measureRejected, realize]

private theorem integral_Q_sqDependence : ObservationalDependence measureSignature integral_Q_sqActual := by
  intro i
  refine ⟨(), Q, 0, ?_⟩
  norm_num [integral_Q_sqActual, realize, integral_Q_sq]

def integral_Q_sqFamily : Registration integral_Q_sqArena (type_of% @integral_Q_sq) where
  actual := integral_Q_sqActual
  bridge := by simp [integral_Q_sqArena, integral_Q_sqActual, realize]
  variation := ⟨by simpa [integral_Q_sqActual, realize] using integral_Q_sq, measureRejected, integral_Q_sqRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integral_Q_sqArena.Law integral_Q_sqActual measureRejected integral_Q_sqRejected
  dependence := integral_Q_sqDependence

def integral_Q_sqAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_Q_sq) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_Q_sqUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.integral_Q_sqFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integral_Q_sqArena⟩
  objectArena := .source ⟨integral_Q_sqArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integral_Q_sqArena ⟨integral_Q_sqFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∫ v : ℝ, v ^ 2 ∂μ) = (51 / 224 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def Q_posActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide ((∀ᵐ v ∂μ, (0 : ℝ) < v))) (fun e => nomatch e)

abbrev Q_posArena : Arena where
  signature := measureSignature
  Law R := R.readout () () Q = true

private theorem Q_posRejected : ¬ Q_posArena.Law measureRejected := by
  simp [Q_posArena, measureRejected, realize]

private theorem Q_posDependence : ObservationalDependence measureSignature Q_posActual := by
  intro i
  refine ⟨(), 0, Measure.dirac (0 : ℝ), ?_⟩
  simp [Q_posActual, realize]

def Q_posFamily : Registration Q_posArena (type_of% @Q_pos) where
  actual := Q_posActual
  bridge := by simp [Q_posArena, Q_posActual, realize]
  variation := ⟨by simpa [Q_posActual, realize] using Q_pos, measureRejected, Q_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    Q_posArena.Law Q_posActual measureRejected Q_posRejected
  dependence := Q_posDependence

def Q_posAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Q_pos) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.Q_posUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.Q_posFamily
  realizationSource := none
  generated := false
  arena := .source ⟨Q_posArena⟩
  objectArena := .source ⟨Q_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Q_posArena ⟨Q_posFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide ((∀ᵐ v ∂μ, (0 : ℝ) < v))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def variance_QActual : Realization measureSignature :=
  realize measureSignature (fun _ _ μ => decide (ProbabilityTheory.variance (fun v : ℝ => v) μ = (771 / 5600 : ℝ))) (fun e => nomatch e)

abbrev variance_QArena : Arena where
  signature := measureSignature
  Law R := R.readout () () Q = true

private theorem variance_QRejected : ¬ variance_QArena.Law measureRejected := by
  simp [variance_QArena, measureRejected, realize]

private theorem variance_QDependence : ObservationalDependence measureSignature variance_QActual := by
  intro i
  refine ⟨(), Q, 0, ?_⟩
  norm_num [variance_QActual, realize, variance_Q]

def variance_QFamily : Registration variance_QArena (type_of% @variance_Q) where
  actual := variance_QActual
  bridge := by simp [variance_QArena, variance_QActual, realize]
  variation := ⟨by simpa [variance_QActual, realize] using variance_Q, measureRejected, variance_QRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    variance_QArena.Law variance_QActual measureRejected variance_QRejected
  dependence := variance_QDependence

def variance_QAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@variance_Q) (Realization measureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.variance_QUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.variance_QFamily
  realizationSource := none
  generated := false
  arena := .source ⟨variance_QArena⟩
  objectArena := .source ⟨variance_QArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source variance_QArena ⟨variance_QFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize measureSignature (fun _ _ μ => decide (ProbabilityTheory.variance (fun v : ℝ => v) μ = (771 / 5600 : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev logarithmSignature := _root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmSignature
abbrev logarithmActual := _root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmActual
abbrev logarithmRejected := _root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmRejected

abbrev stieltjesArena : Arena where
  signature := logarithmSignature
  Law R := ∀ {x : ℝ}, 0 < x → R.readout () () x = x / 8 * ∫ v, 1 / (x ^ 2 + v) ∂P

private theorem stieltjesRejected : ¬ stieltjesArena.Law logarithmRejected := by
  intro h
  have h0 := h (x := 1) zero_lt_one
  change 0 = _ at h0
  have h1 := r_eq_stieltjes (x := 1) zero_lt_one
  linarith [_root_.D5.S3.Analytic.WallisRemainder.Laplace.r_pos (x := 1) zero_lt_one]

private theorem logarithmDependence : ObservationalDependence logarithmSignature logarithmActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change -Real.log (wallisB 0) ≠ -Real.log (wallisB 1)
  rw [show wallisB 0 = 0 by simp [wallisB], Real.log_zero, neg_zero]
  exact (_root_.D5.S3.Analytic.WallisRemainder.Laplace.r_pos (x := 1) zero_lt_one).ne

def stieltjesFamily : Registration stieltjesArena (type_of% @r_eq_stieltjes) where
  actual := logarithmActual
  bridge := Iff.rfl
  variation := ⟨r_eq_stieltjes, logarithmRejected, stieltjesRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    stieltjesArena.Law logarithmActual logarithmRejected stieltjesRejected
  dependence := logarithmDependence

def stieltjesAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@r_eq_stieltjes) (Realization logarithmSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.stieltjesUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.stieltjesFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stieltjesArena⟩
  objectArena := .source ⟨stieltjesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stieltjesArena ⟨stieltjesFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize logarithmSignature (fun _ _ x => -Real.log (wallisB x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev weightSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ n => spectralWeight n) (fun e => nomatch e)

def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature
  Law R := HasSum (R.readout () ()) 1

private theorem weightNegative : ¬ weightArena.Law weightRejected := by
  intro h
  have he := (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).unique h
  norm_num at he

private theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change spectralWeight 0 ≠ spectralWeight 1
  norm_num [spectralWeight]
  intro h
  field_simp at h
  nlinarith [sq_pos_of_pos Real.pi_pos]

def weightFamily : Registration weightArena (type_of% @hasSum_spectralWeight) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨hasSum_spectralWeight, weightRejected, weightNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    weightArena.Law weightActual weightRejected weightNegative
  dependence := weightDependence

abbrev fractionSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def fractionActual : Realization fractionSignature :=
  realize fractionSignature
    (fun _ u n => 8 / (Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * u ^ 2))
    (fun e => nomatch e)

def fractionRejected : Realization fractionSignature :=
  realize fractionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fractionArena : Arena where
  signature := fractionSignature
  Law R := ∀ {u : ℝ}, 0 < u → HasSum (R.readout () u) (Real.tanh u / u)

private theorem fractionNegative : ¬ fractionArena.Law fractionRejected := by
  intro h
  have he := (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).unique
    (h (u := 1) zero_lt_one)
  have hp : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr zero_lt_one) (Real.cosh_pos _)
  norm_num at he
  linarith

private theorem fractionDependence : ObservationalDependence fractionSignature fractionActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [fractionActual, realize]
  intro h
  field_simp at h
  nlinarith [sq_pos_of_pos Real.pi_pos]

def fractionFamily : Registration fractionArena (type_of% @tanh_div_hasSum) where
  actual := fractionActual
  bridge := Iff.rfl
  variation := ⟨tanh_div_hasSum, fractionRejected, fractionNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    fractionArena.Law fractionActual fractionRejected fractionNegative
  dependence := fractionDependence

abbrev biasSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ)

def biasActual : Realization biasSignature :=
  realize biasSignature (fun _ _ f => ∫ v, f v ∂Q) (fun e => nomatch e)

def biasRejected : Realization biasSignature :=
  realize biasSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev biasArena : Arena where
  signature := biasSignature
  Law R := ∀ (f : ℝ → ℝ), R.readout () () f = 24 * ∫ v, v * f v ∂P

private theorem biasNegative : ¬ biasArena.Law biasRejected := by
  intro h
  have he := h (fun _ => 1)
  norm_num [biasRejected, realize, integral_P_id] at he

private theorem biasDependence : ObservationalDependence biasSignature biasActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [biasActual, realize]

def biasFamily : Registration biasArena (type_of% @integral_Q) where
  actual := biasActual
  bridge := Iff.rfl
  variation := ⟨integral_Q, biasRejected, biasNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    biasArena.Law biasActual biasRejected biasNegative
  dependence := biasDependence

def weightAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasSum_spectralWeight) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.weightUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.weightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ n => spectralWeight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fractionAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tanh_div_hasSum) (Realization fractionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.fractionUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.fractionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fractionArena⟩
  objectArena := .source ⟨fractionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fractionArena ⟨fractionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fractionSignature (fun _ u n => 8 / (Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * u ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def biasAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_Q) (Realization biasSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.biasUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.biasFamily
  realizationSource := none
  generated := false
  arena := .source ⟨biasArena⟩
  objectArena := .source ⟨biasArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source biasArena ⟨biasFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize biasSignature (fun _ _ f => ∫ v, f v ∂Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.WallisRemainder.Measure
