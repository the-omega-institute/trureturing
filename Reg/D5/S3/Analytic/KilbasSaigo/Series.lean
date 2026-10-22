import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KilbasSaigo.Series
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.KilbasSaigo.Series
open _root_.D5.S3.Analytic.KilbasSaigo.Defs
open _root_.D5.S3.Analytic.KilbasSaigo.Series
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
noncomputable section

abbrev baseSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def baseActual : Realization baseSignature :=
  realize baseSignature (fun _ α m => 1 + α * m) (fun e => nomatch e)

def baseZero : Realization baseSignature :=
  realize baseSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem baseDependence : ObservationalDependence baseSignature baseActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [baseActual, realize]

abbrev phiSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℝ → ℝ)

def phiActual : Realization phiSignature :=
  realize phiSignature (fun _ α m => phi α m) (fun e => nomatch e)

def phiZero : Realization phiSignature :=
  realize phiSignature (fun _ _ _ _ _ => 0) (fun e => nomatch e)
def phiOne : Realization phiSignature :=
  realize phiSignature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

private theorem phiDependence : ObservationalDependence phiSignature phiActual := by
  intro i
  refine ⟨1, 0, -1, ?_⟩
  intro he
  have hh := congrArg (fun f : ℝ → ℝ → ℝ => f 0 0) he
  norm_num [phiActual, realize, phi] at hh

abbrev coeffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℕ → ℝ)

def coeffActual : Realization coeffSignature :=
  realize coeffSignature (fun _ α m => ksCoeff α m) (fun e => nomatch e)

def coeffZero : Realization coeffSignature :=
  realize coeffSignature (fun _ _ _ _ _ => 0) (fun e => nomatch e)
def coeffOne : Realization coeffSignature :=
  realize coeffSignature (fun _ _ _ _ _ => 1) (fun e => nomatch e)
def coeffShift : Realization coeffSignature :=
  realize coeffSignature (fun _ α m l n => ksCoeff α m l n + 1) (fun e => nomatch e)

private theorem coeffDependence : ObservationalDependence coeffSignature coeffActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have hh := congrArg (fun f : ℝ → ℕ → ℝ => f 0 2) he
  norm_num [coeffActual, realize, ksCoeff, Finset.prod_range_succ] at hh

abbrev dcoeffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℕ → ℕ → ℝ)

def dcoeffActual : Realization dcoeffSignature :=
  realize dcoeffSignature (fun _ α m => gCoeff α m) (fun e => nomatch e)

def dcoeffOne : Realization dcoeffSignature :=
  realize dcoeffSignature (fun _ _ _ _ _ _ => 1) (fun e => nomatch e)
def dcoeffShift : Realization dcoeffSignature :=
  realize dcoeffSignature (fun _ α m l k n => gCoeff α m l k n + 1) (fun e => nomatch e)

private theorem dcoeffDependence : ObservationalDependence dcoeffSignature dcoeffActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have hh := congrArg (fun f : ℝ → ℕ → ℕ → ℝ => f 0 0 2) he
  norm_num [dcoeffActual, realize, gCoeff, ksCoeff, Finset.prod_range_succ] at hh

abbrev gSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℕ → ℝ → ℝ)

def gActual : Realization gSignature :=
  realize gSignature (fun _ α m => g α m) (fun e => nomatch e)

def gZero : Realization gSignature :=
  realize gSignature (fun _ _ _ _ _ _ => 0) (fun e => nomatch e)
def gShift : Realization gSignature :=
  realize gSignature (fun _ α m l k x => g α m l k x + 1) (fun e => nomatch e)
def gJump : Realization gSignature :=
  realize gSignature (fun _ _ _ _ _ x => if x = 0 then 0 else 1) (fun e => nomatch e)

private theorem gDependence : ObservationalDependence gSignature gActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have hh := congrArg (fun f : ℝ → ℕ → ℝ → ℝ => f 0 2 0) he
  norm_num [gActual, realize, g_zero, ksCoeff, Finset.prod_range_succ] at hh

def base_posArena : Arena where
  signature := baseSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hl : m - 1 / α < l), 0 < R.readout () α (l - m)

private theorem base_posRejected : ¬ base_posArena.Law baseZero := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num)
  norm_num [baseZero, realize] at hh

def base_posEvidence : Registration base_posArena (type_of% @base_pos) where
  actual := baseActual
  bridge := Iff.rfl
  variation := ⟨@base_pos, baseZero, base_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    base_posArena.Law baseActual baseZero base_posRejected
  dependence := baseDependence

def base_posAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@base_pos) (Realization baseSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.base_posUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.base_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨base_posArena⟩
  objectArena := .source ⟨base_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source base_posArena ⟨base_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize baseSignature (fun _ α m => 1 + α * m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def phi_posArena : Arena where
  signature := phiSignature
  Law R := ∀ {α m l s : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l) (_hs : 0 ≤ s), 0 < R.readout () α m l s

private theorem phi_posRejected : ¬ phi_posArena.Law phiZero := by
  intro h
  have hh := @h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [phiZero, realize] at hh

def phi_posEvidence : Registration phi_posArena (type_of% @phi_pos) where
  actual := phiActual
  bridge := Iff.rfl
  variation := ⟨@phi_pos, phiZero, phi_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    phi_posArena.Law phiActual phiZero phi_posRejected
  dependence := phiDependence

def phi_posAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phi_pos) (Realization phiSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.phi_posUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.phi_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨phi_posArena⟩
  objectArena := .source ⟨phi_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source phi_posArena ⟨phi_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phiSignature (fun _ α m => phi α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def ksCoeff_succArena : Arena where
  signature := coeffSignature
  Law R := ∀ (α m l : ℝ) (n : ℕ), R.readout () α m l (n + 1) = ksCoeff α m l n / phi α m l (n + 1)

private theorem ksCoeff_succRejected : ¬ ksCoeff_succArena.Law coeffShift := by
  intro h
  have hh := h 1 1 1 0
  change ksCoeff 1 1 1 (0 + 1) + 1 = _ at hh
  have ht := ksCoeff_succ 1 1 1 0
  linarith

def ksCoeff_succEvidence : Registration ksCoeff_succArena (type_of% @ksCoeff_succ) where
  actual := coeffActual
  bridge := Iff.rfl
  variation := ⟨@ksCoeff_succ, coeffShift, ksCoeff_succRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    ksCoeff_succArena.Law coeffActual coeffShift ksCoeff_succRejected
  dependence := coeffDependence

def ksCoeff_succAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ksCoeff_succ) (Realization coeffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.ksCoeff_succUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.ksCoeff_succEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨ksCoeff_succArena⟩
  objectArena := .source ⟨ksCoeff_succArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ksCoeff_succArena ⟨ksCoeff_succEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coeffSignature (fun _ α m => ksCoeff α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def ksCoeff_posArena : Arena where
  signature := coeffSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), ∀ (n : ℕ), 0 < R.readout () α m l n

private theorem ksCoeff_posRejected : ¬ ksCoeff_posArena.Law coeffZero := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0
  norm_num [coeffZero, realize] at hh

def ksCoeff_posEvidence : Registration ksCoeff_posArena (type_of% @ksCoeff_pos) where
  actual := coeffActual
  bridge := Iff.rfl
  variation := ⟨@ksCoeff_pos, coeffZero, ksCoeff_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    ksCoeff_posArena.Law coeffActual coeffZero ksCoeff_posRejected
  dependence := coeffDependence

def ksCoeff_posAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ksCoeff_pos) (Realization coeffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.ksCoeff_posUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.ksCoeff_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨ksCoeff_posArena⟩
  objectArena := .source ⟨ksCoeff_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ksCoeff_posArena ⟨ksCoeff_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coeffSignature (fun _ α m => ksCoeff α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def inv_phi_eq_betaArena : Arena where
  signature := phiSignature
  Law R := ∀ {α m l s : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l) (_hs : 0 ≤ s), 1 / R.readout () α m l s = (Real.Gamma α)⁻¹ * ∫ r in (0 : ℝ)..1, r ^ (1 + α * (l - m) + α * m * s - 1) * (1 - r) ^ (α - 1)

private theorem inv_phi_eq_betaRejected : ¬ inv_phi_eq_betaArena.Law phiZero := by
  intro h
  have hh := @h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [phiZero, realize, div_zero] at hh
  have ht := inv_phi_eq_beta (α := 1) (m := 1) (l := 1) (s := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := one_div_pos.mpr (phi_pos (α := 1) (m := 1) (l := 1) (s := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  linarith

def inv_phi_eq_betaEvidence : Registration inv_phi_eq_betaArena (type_of% @inv_phi_eq_beta) where
  actual := phiActual
  bridge := Iff.rfl
  variation := ⟨@inv_phi_eq_beta, phiZero, inv_phi_eq_betaRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    inv_phi_eq_betaArena.Law phiActual phiZero inv_phi_eq_betaRejected
  dependence := phiDependence

def inv_phi_eq_betaAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inv_phi_eq_beta) (Realization phiSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.inv_phi_eq_betaUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.inv_phi_eq_betaEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨inv_phi_eq_betaArena⟩
  objectArena := .source ⟨inv_phi_eq_betaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inv_phi_eq_betaArena ⟨inv_phi_eq_betaEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phiSignature (fun _ α m => phi α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def tendsto_inv_phiArena : Arena where
  signature := phiSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), Tendsto (fun n : ℕ => 1 / R.readout () α m l n) atTop (𝓝 0)

private theorem tendsto_inv_phiRejected : ¬ tendsto_inv_phiArena.Law phiOne := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  simp only [phiOne, realize, div_one] at hh
  have he := tendsto_nhds_unique hh (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  norm_num at he

def tendsto_inv_phiEvidence : Registration tendsto_inv_phiArena (type_of% @tendsto_inv_phi) where
  actual := phiActual
  bridge := Iff.rfl
  variation := ⟨@tendsto_inv_phi, phiOne, tendsto_inv_phiRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tendsto_inv_phiArena.Law phiActual phiOne tendsto_inv_phiRejected
  dependence := phiDependence

def tendsto_inv_phiAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tendsto_inv_phi) (Realization phiSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.tendsto_inv_phiUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.tendsto_inv_phiEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨tendsto_inv_phiArena⟩
  objectArena := .source ⟨tendsto_inv_phiArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tendsto_inv_phiArena ⟨tendsto_inv_phiEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phiSignature (fun _ α m => phi α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gCoeff_succArena : Arena where
  signature := dcoeffSignature
  Law R := ∀ (α m l : ℝ) (k n : ℕ), R.readout () α m l k (n + 1) = (((n : ℝ) + k + 1) / (n + 1) / phi α m l (n + k + 1)) * gCoeff α m l k n

private theorem gCoeff_succRejected : ¬ gCoeff_succArena.Law dcoeffShift := by
  intro h
  have hh := h 1 1 1 0 0
  change gCoeff 1 1 1 0 (0 + 1) + 1 = _ at hh
  have ht := gCoeff_succ 1 1 1 0 0
  linarith

def gCoeff_succEvidence : Registration gCoeff_succArena (type_of% @gCoeff_succ) where
  actual := dcoeffActual
  bridge := Iff.rfl
  variation := ⟨@gCoeff_succ, dcoeffShift, gCoeff_succRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    gCoeff_succArena.Law dcoeffActual dcoeffShift gCoeff_succRejected
  dependence := dcoeffDependence

def gCoeff_succAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gCoeff_succ) (Realization dcoeffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.gCoeff_succUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.gCoeff_succEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gCoeff_succArena⟩
  objectArena := .source ⟨gCoeff_succArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gCoeff_succArena ⟨gCoeff_succEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dcoeffSignature (fun _ α m => gCoeff α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gCoeff_stepArena : Arena where
  signature := dcoeffSignature
  Law R := ∀ (α m l : ℝ) (k n : ℕ), ((n : ℝ) + 1) * R.readout () α m l k (n + 1) = gCoeff α m l (k + 1) n

private theorem gCoeff_stepRejected : ¬ gCoeff_stepArena.Law dcoeffShift := by
  intro h
  have hh := h 1 1 1 0 0
  simp only [dcoeffShift, realize, Nat.cast_zero, zero_add, one_mul] at hh
  have ht := gCoeff_step 1 1 1 0 0
  norm_num only [Nat.cast_zero, zero_add, one_mul] at ht
  linarith

def gCoeff_stepEvidence : Registration gCoeff_stepArena (type_of% @gCoeff_step) where
  actual := dcoeffActual
  bridge := Iff.rfl
  variation := ⟨@gCoeff_step, dcoeffShift, gCoeff_stepRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    gCoeff_stepArena.Law dcoeffActual dcoeffShift gCoeff_stepRejected
  dependence := dcoeffDependence

def gCoeff_stepAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gCoeff_step) (Realization dcoeffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.gCoeff_stepUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.gCoeff_stepEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gCoeff_stepArena⟩
  objectArena := .source ⟨gCoeff_stepArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gCoeff_stepArena ⟨gCoeff_stepEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dcoeffSignature (fun _ α m => gCoeff α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def summable_gCoeffArena : Arena where
  signature := dcoeffSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), ∀ (k : ℕ) (z : ℝ), Summable (fun n => R.readout () α m l k n * z ^ n)

private theorem summable_gCoeffRejected : ¬ summable_gCoeffArena.Law dcoeffOne := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0 1
  simp only [dcoeffOne, realize, one_pow, mul_one] at hh
  simp only [summable_const_iff, one_ne_zero] at hh

def summable_gCoeffEvidence : Registration summable_gCoeffArena (type_of% @summable_gCoeff) where
  actual := dcoeffActual
  bridge := Iff.rfl
  variation := ⟨@summable_gCoeff, dcoeffOne, summable_gCoeffRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    summable_gCoeffArena.Law dcoeffActual dcoeffOne summable_gCoeffRejected
  dependence := dcoeffDependence

def summable_gCoeffAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_gCoeff) (Realization dcoeffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.summable_gCoeffUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.summable_gCoeffEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨summable_gCoeffArena⟩
  objectArena := .source ⟨summable_gCoeffArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source summable_gCoeffArena ⟨summable_gCoeffEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dcoeffSignature (fun _ α m => gCoeff α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def summable_kilbasSaigoArena : Arena where
  signature := coeffSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), ∀ (z : ℝ), Summable (fun n => R.readout () α m l n * z ^ n)

private theorem summable_kilbasSaigoRejected : ¬ summable_kilbasSaigoArena.Law coeffOne := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 1
  simp only [coeffOne, realize, one_pow, mul_one] at hh
  simp only [summable_const_iff, one_ne_zero] at hh

def summable_kilbasSaigoEvidence : Registration summable_kilbasSaigoArena (type_of% @summable_kilbasSaigo) where
  actual := coeffActual
  bridge := Iff.rfl
  variation := ⟨@summable_kilbasSaigo, coeffOne, summable_kilbasSaigoRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    summable_kilbasSaigoArena.Law coeffActual coeffOne summable_kilbasSaigoRejected
  dependence := coeffDependence

def summable_kilbasSaigoAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_kilbasSaigo) (Realization coeffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.summable_kilbasSaigoUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.summable_kilbasSaigoEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨summable_kilbasSaigoArena⟩
  objectArena := .source ⟨summable_kilbasSaigoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source summable_kilbasSaigoArena ⟨summable_kilbasSaigoEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coeffSignature (fun _ α m => ksCoeff α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def g_zeroArena : Arena where
  signature := gSignature
  Law R := ∀ (α m l : ℝ) (k : ℕ), R.readout () α m l k 0 = (k.factorial : ℝ) * ksCoeff α m l k

private theorem g_zeroRejected : ¬ g_zeroArena.Law gShift := by
  intro h
  have hh := h 1 1 1 0
  change g 1 1 1 0 0 + 1 = _ at hh
  have ht := g_zero 1 1 1 0
  linarith

def g_zeroEvidence : Registration g_zeroArena (type_of% @g_zero) where
  actual := gActual
  bridge := Iff.rfl
  variation := ⟨@g_zero, gShift, g_zeroRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    g_zeroArena.Law gActual gShift g_zeroRejected
  dependence := gDependence

def g_zeroAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@g_zero) (Realization gSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.g_zeroUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.g_zeroEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨g_zeroArena⟩
  objectArena := .source ⟨g_zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source g_zeroArena ⟨g_zeroEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gSignature (fun _ α m => g α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def g_zero_posArena : Arena where
  signature := gSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), ∀ (k : ℕ), 0 < R.readout () α m l k 0

private theorem g_zero_posRejected : ¬ g_zero_posArena.Law gZero := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0
  norm_num [gZero, realize] at hh

def g_zero_posEvidence : Registration g_zero_posArena (type_of% @g_zero_pos) where
  actual := gActual
  bridge := Iff.rfl
  variation := ⟨@g_zero_pos, gZero, g_zero_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    g_zero_posArena.Law gActual gZero g_zero_posRejected
  dependence := gDependence

def g_zero_posAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@g_zero_pos) (Realization gSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.g_zero_posUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.g_zero_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨g_zero_posArena⟩
  objectArena := .source ⟨g_zero_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source g_zero_posArena ⟨g_zero_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gSignature (fun _ α m => g α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def kilbasSaigo_neg_eq_g0Arena : Arena where
  signature := gSignature
  Law R := ∀ (α m l x : ℝ), kilbasSaigo α m l (-x) = R.readout () α m l 0 x

private theorem kilbasSaigo_neg_eq_g0Rejected : ¬ kilbasSaigo_neg_eq_g0Arena.Law gShift := by
  intro h
  have hh := h 1 1 1 0
  change kilbasSaigo 1 1 1 (-0) = g 1 1 1 0 0 + 1 at hh
  have ht := kilbasSaigo_neg_eq_g0 1 1 1 0
  linarith

def kilbasSaigo_neg_eq_g0Evidence : Registration kilbasSaigo_neg_eq_g0Arena (type_of% @kilbasSaigo_neg_eq_g0) where
  actual := gActual
  bridge := Iff.rfl
  variation := ⟨@kilbasSaigo_neg_eq_g0, gShift, kilbasSaigo_neg_eq_g0Rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    kilbasSaigo_neg_eq_g0Arena.Law gActual gShift kilbasSaigo_neg_eq_g0Rejected
  dependence := gDependence

def kilbasSaigo_neg_eq_g0Audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kilbasSaigo_neg_eq_g0) (Realization gSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.kilbasSaigo_neg_eq_g0Unit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.kilbasSaigo_neg_eq_g0Evidence
  realizationSource := none
  generated := false
  arena := .source ⟨kilbasSaigo_neg_eq_g0Arena⟩
  objectArena := .source ⟨kilbasSaigo_neg_eq_g0Arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kilbasSaigo_neg_eq_g0Arena ⟨kilbasSaigo_neg_eq_g0Evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gSignature (fun _ α m => g α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def hasDerivAt_gArena : Arena where
  signature := gSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), ∀ (k : ℕ) (x : ℝ), HasDerivAt (R.readout () α m l k) (-g α m l (k + 1) x) x

private theorem hasDerivAt_gRejected : ¬ hasDerivAt_gArena.Law gZero := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0 0
  change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-g 1 1 1 (0 + 1) 0) 0 at hh
  have he := hh.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hp := g_zero_pos (α := 1) (m := 1) (l := 1)
    (by norm_num) (by norm_num) (by norm_num) 1
  norm_num at he
  linarith

def hasDerivAt_gEvidence : Registration hasDerivAt_gArena (type_of% @hasDerivAt_g) where
  actual := gActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_g, gZero, hasDerivAt_gRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hasDerivAt_gArena.Law gActual gZero hasDerivAt_gRejected
  dependence := gDependence

def hasDerivAt_gAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_g) (Realization gSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.hasDerivAt_gUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.hasDerivAt_gEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨hasDerivAt_gArena⟩
  objectArena := .source ⟨hasDerivAt_gArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hasDerivAt_gArena ⟨hasDerivAt_gEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gSignature (fun _ α m => g α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def continuous_gArena : Arena where
  signature := gSignature
  Law R := ∀ {α m l : ℝ} (_hα : 0 < α) (_hm : 0 < m) (_hl : m - 1 / α < l), ∀ (k : ℕ), Continuous (R.readout () α m l k)

private theorem continuous_gRejected : ¬ continuous_gArena.Law gJump := by
  intro h
  have hh := @h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0
  change Continuous (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) at hh
  obtain ⟨d, hd, hb⟩ := Metric.continuousAt_iff.mp hh.continuousAt (1/2) (by norm_num)
  have hy : d / 2 ≠ 0 := by positivity
  have hdist : dist (d / 2) (0 : ℝ) < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have he := hb hdist
  norm_num [hy] at he

def continuous_gEvidence : Registration continuous_gArena (type_of% @continuous_g) where
  actual := gActual
  bridge := Iff.rfl
  variation := ⟨@continuous_g, gJump, continuous_gRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    continuous_gArena.Law gActual gJump continuous_gRejected
  dependence := gDependence

def continuous_gAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_g) (Realization gSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.continuous_gUnit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Series.continuous_gEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨continuous_gArena⟩
  objectArena := .source ⟨continuous_gArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source continuous_gArena ⟨continuous_gEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gSignature (fun _ α m => g α m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.KilbasSaigo.Series
