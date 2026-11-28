import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
import Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.Orbits
import Reg.Support.SingleDependentReadout

/-! Dependent readouts for Kerr geometry and horizon mechanics. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D

set_option autoImplicit false

noncomputable section

abbrev radialSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def radialActual : Realization radialSignature :=
  realize radialSignature (fun _ p r => kerrDelta p.1 p.2 r) (fun e => nomatch e)

def radialErased : Realization radialSignature :=
  realize radialSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev radialArena : Arena where
  signature := radialSignature
  Law R := ∀ {M a : ℝ}, |a| ≤ M → ∀ r : ℝ,
    R.readout () ⟨M, a⟩ r = (r - rPlus M a) * (r - rMinus M a)

private theorem radial_erasure_changes_factorization : ¬ radialArena.Law radialErased := by
  intro h
  have he := h (M := 0) (a := 0) (by norm_num) 1
  change (0 : ℝ) = (1 - rPlus 0 0) * (1 - rMinus 0 0) at he
  norm_num [rPlus, rMinus] at he

def radialFamily : Registration radialArena (type_of% (@kerrDelta_factorization)) where
  actual := radialActual
  bridge := Iff.rfl
  variation := ⟨@kerrDelta_factorization, radialErased, radial_erasure_changes_factorization⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    radialArena.Law radialActual radialErased radial_erasure_changes_factorization
  dependence := by
    intro _
    refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
    change kerrDelta 0 0 0 ≠ kerrDelta 0 0 1
    norm_num [kerrDelta]

def radialRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kerrDelta_factorization) (Realization radialSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.kerrDelta_factorization.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.radialFamily
  realizationSource := none
  generated := false
  arena := .source ⟨radialArena⟩
  objectArena := .source ⟨radialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source radialArena ⟨radialFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize radialSignature
    (fun _ p r => kerrDelta p.1 p.2 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev fluxParameters := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ

abbrev fluxSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature fluxParameters (fun _ => ℝ) (fun _ => ℝ)

def fluxActual : Realization fluxSignature :=
  realize fluxSignature (fun _ p coefficient => horizonAbsorption p.1 p.2.1 p.2.2.2 p.2.2.1 coefficient)
    (fun e => nomatch e)

def fluxErased : Realization fluxSignature :=
  realize fluxSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fluxArena : Arena where
  signature := fluxSignature
  Law R := ∀ (M a m : ℝ) {ω coefficient : ℝ}, 0 < ω → 0 < coefficient →
    (R.readout () ⟨M, a, m, ω⟩ coefficient < 0 ↔ ω < m * horizonOmega M a)

private theorem flux_erasure_loses_threshold : ¬ fluxArena.Law fluxErased := by
  intro h
  have he := h 1 1 4 (ω := 1) (coefficient := 1) (by norm_num) (by norm_num)
  change (0 : ℝ) < 0 ↔ 1 < 4 * horizonOmega 1 1 at he
  norm_num [horizonOmega, rPlus] at he

def fluxFamily : Registration fluxArena (type_of% (@superradiance_condition_iff)) where
  actual := fluxActual
  bridge := Iff.rfl
  variation := ⟨@superradiance_condition_iff, fluxErased, flux_erasure_loses_threshold⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    fluxArena.Law fluxActual fluxErased flux_erasure_loses_threshold
  dependence := by
    intro _
    refine ⟨⟨1, 0, 1, 1⟩, 1, 2, ?_⟩
    change horizonAbsorption 1 0 1 1 1 ≠ horizonAbsorption 1 0 1 1 2
    norm_num [horizonAbsorption, horizonOmega]

def fluxRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@superradiance_condition_iff) (Realization fluxSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.superradiance_condition_iff.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.fluxFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fluxArena⟩
  objectArena := .source ⟨fluxArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fluxArena ⟨fluxFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fluxSignature
    (fun _ p coefficient => horizonAbsorption p.1 p.2.1 p.2.2.2 p.2.2.1 coefficient) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev metricSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def metricActual : Realization metricSignature :=
  realize metricSignature
    (fun _ p θ => g_tt p.1 p.2.1 p.2.2 θ * g_φφ p.1 p.2.1 p.2.2 θ -
      g_tφ p.1 p.2.1 p.2.2 θ ^ 2) (fun e => nomatch e)

def metricErased : Realization metricSignature :=
  realize metricSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev metricArena : Arena where
  signature := metricSignature
  Law R := ∀ {M a r θ : ℝ}, kerrSigma a r θ ≠ 0 →
    R.readout () ⟨M, a, r⟩ θ = -kerrDelta M a r * Real.sin θ ^ 2

private theorem metric_erasure_loses_determinant : ¬ metricArena.Law metricErased := by
  intro h
  have he := h (M := 0) (a := 0) (r := 1) (θ := Real.pi / 2) (by norm_num [kerrSigma])
  change (0 : ℝ) = -kerrDelta 0 0 1 * Real.sin (Real.pi / 2) ^ 2 at he
  norm_num [kerrDelta, Real.sin_pi_div_two] at he

def metricFamily : Registration metricArena (type_of% (@kerr_metric_2d_det)) where
  actual := metricActual
  bridge := Iff.rfl
  variation := ⟨@kerr_metric_2d_det, metricErased, metric_erasure_loses_determinant⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    metricArena.Law metricActual metricErased metric_erasure_loses_determinant
  dependence := by
    intro _
    refine ⟨⟨0, 0, 1⟩, 0, Real.pi / 2, ?_⟩
    have h₁ : kerrSigma 0 1 0 ≠ 0 := by norm_num [kerrSigma]
    have h₂ : kerrSigma 0 1 (Real.pi / 2) ≠ 0 := by norm_num [kerrSigma]
    change
      g_tt 0 0 1 0 * g_φφ 0 0 1 0 - g_tφ 0 0 1 0 ^ 2 ≠
      g_tt 0 0 1 (Real.pi / 2) * g_φφ 0 0 1 (Real.pi / 2) - g_tφ 0 0 1 (Real.pi / 2) ^ 2
    rw [kerr_metric_2d_det h₁, kerr_metric_2d_det h₂]
    norm_num [kerrDelta, Real.sin_pi_div_two]

abbrev rigiditySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def rigidityActual : Realization rigiditySignature :=
  realize rigiditySignature (fun _ M a => horizonOmega M a) (fun e => nomatch e)

def rigidityErased : Realization rigiditySignature :=
  realize rigiditySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev rigidityArena : Arena where
  signature := rigiditySignature
  Law R := ∀ {M a θ : ℝ}, 0 < M → |a| ≤ M → Real.sin θ ≠ 0 →
    frameDragOmega M a (rPlus M a) θ = R.readout () M a

private theorem rigidity_erasure_loses_horizon_velocity : ¬ rigidityArena.Law rigidityErased := by
  intro h
  have hm : 0 < (1 : ℝ) := by norm_num
  have ha : |(1 : ℝ)| ≤ 1 := by norm_num
  have hs : Real.sin (Real.pi / 2) ≠ 0 := by simp [Real.sin_pi_div_two]
  have he := h hm ha hs
  change frameDragOmega 1 1 (rPlus 1 1) (Real.pi / 2) = 0 at he
  rw [frameDrag_at_horizon_rigid hm ha hs] at he
  norm_num [horizonOmega, rPlus] at he

def rigidityFamily : Registration rigidityArena (type_of% (@frameDrag_at_horizon_rigid)) where
  actual := rigidityActual
  bridge := Iff.rfl
  variation := ⟨@frameDrag_at_horizon_rigid, rigidityErased, rigidity_erasure_loses_horizon_velocity⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    rigidityArena.Law rigidityActual rigidityErased rigidity_erasure_loses_horizon_velocity
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    change horizonOmega 1 0 ≠ horizonOmega 1 1
    norm_num [horizonOmega, rPlus]

abbrev circularParameters := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ

abbrev circularSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature circularParameters
    (fun _ => ℝ) (fun _ => ℝ)

def circularActual : Realization circularSignature :=
  realize circularSignature (fun _ p Ω => circularNorm p.1 p.2.1 p.2.2.1 p.2.2.2 Ω)
    (fun e => nomatch e)

def circularZero : Realization circularSignature :=
  realize circularSignature (fun _ _ _ => 0) (fun e => nomatch e)

def circularNegative : Realization circularSignature :=
  realize circularSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem circular_dependence : ObservationalDependence circularSignature circularActual := by
  intro _
  refine ⟨⟨1, 1, 3 / 2, Real.pi / 2⟩, 0, 1, ?_⟩
  change circularNorm 1 1 (3 / 2) (Real.pi / 2) 0 ≠
    circularNorm 1 1 (3 / 2) (Real.pi / 2) 1
  norm_num [circularNorm, g_tt, g_tφ, g_φφ, kerrA, kerrDelta, kerrSigma,
    Real.sin_pi_div_two, Real.cos_pi_div_two]

abbrev timelikeArena : Arena where
  signature := circularSignature
  Law R := ∀ {M a r θ Ω : ℝ}, 0 < M → |a| ≤ M → rPlus M a < r → Real.sin θ ≠ 0 →
    (R.readout () ⟨M, a, r, θ⟩ Ω < 0 ↔ omegaMin M a r θ < Ω ∧ Ω < omegaMax M a r θ)

private theorem circular_erasure_loses_timelike : ¬ timelikeArena.Law circularZero := by
  intro h
  have hm : 0 < (1 : ℝ) := by norm_num
  have ha : |(0 : ℝ)| ≤ 1 := by norm_num
  have hr : rPlus 1 0 < 3 := by norm_num [rPlus]
  have hs : Real.sin (Real.pi / 2) ≠ 0 := by simp [Real.sin_pi_div_two]
  have hn : circularNorm 1 0 3 (Real.pi / 2) 0 < 0 := by
    norm_num [circularNorm, g_tt, kerrSigma]
  have hw := (timelike_omega_window_iff hm ha hr hs).1 hn
  exact (lt_irrefl (0 : ℝ)) ((h hm ha hr hs).2 hw)

def timelikeFamily : Registration timelikeArena (type_of% (@timelike_omega_window_iff)) where
  actual := circularActual
  bridge := Iff.rfl
  variation := ⟨@timelike_omega_window_iff, circularZero, circular_erasure_loses_timelike⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    timelikeArena.Law circularActual circularZero circular_erasure_loses_timelike
  dependence := circular_dependence

abbrev corotationArena : Arena where
  signature := circularSignature
  Law R := ∀ {M a r θ : ℝ}, 0 < a → a ≤ M → rPlus M a < r → r < rErgo M a θ →
    Real.sin θ ≠ 0 →
    0 < omegaMin M a r θ ∧ 0 < circularNorm M a r θ 0 ∧
      ∀ Ω : ℝ, R.readout () ⟨M, a, r, θ⟩ Ω < 0 → 0 < Ω

private theorem circular_replacement_breaks_corotation :
    ¬ corotationArena.Law circularNegative := by
  intro h
  have ha : 0 < (1 : ℝ) := by norm_num
  have hr : rPlus 1 1 < 3 / 2 := by norm_num [rPlus]
  have he : (3 / 2 : ℝ) < rErgo 1 1 (Real.pi / 2) := by norm_num [rErgo, Real.cos_pi_div_two]
  have hs : Real.sin (Real.pi / 2) ≠ 0 := by simp [Real.sin_pi_div_two]
  have hn : circularNegative.readout () ⟨1, 1, 3 / 2, Real.pi / 2⟩ 0 < 0 := by
    change (-1 : ℝ) < 0
    norm_num
  exact (lt_irrefl (0 : ℝ)) ((h ha le_rfl hr he hs).2.2 0 hn)

def corotationFamily : Registration corotationArena
    (type_of% (@ergosphere_forbids_static_observer)) where
  actual := circularActual
  bridge := Iff.rfl
  variation := ⟨@ergosphere_forbids_static_observer, circularNegative,
    circular_replacement_breaks_corotation⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    corotationArena.Law circularActual circularNegative circular_replacement_breaks_corotation
  dependence := circular_dependence

def metricRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kerr_metric_2d_det) (Realization metricSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.kerr_metric_2d_det.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.metricFamily
  realizationSource := none
  generated := false
  arena := .source ⟨metricArena⟩
  objectArena := .source ⟨metricArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source metricArena ⟨metricFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize metricSignature
    (fun _ p θ => g_tt p.1 p.2.1 p.2.2 θ * g_φφ p.1 p.2.1 p.2.2 θ -
      g_tφ p.1 p.2.1 p.2.2 θ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def rigidityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@frameDrag_at_horizon_rigid) (Realization rigiditySignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.frameDrag_at_horizon_rigid.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.rigidityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rigidityArena⟩
  objectArena := .source ⟨rigidityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rigidityArena ⟨rigidityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rigiditySignature
    (fun _ M a => horizonOmega M a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def timelikeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@timelike_omega_window_iff) (Realization circularSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.timelike_omega_window_iff.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.timelikeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨timelikeArena⟩
  objectArena := .source ⟨timelikeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timelikeArena ⟨timelikeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize circularSignature
    (fun _ p Ω => circularNorm p.1 p.2.1 p.2.2.1 p.2.2.2 Ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def corotationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ergosphere_forbids_static_observer) (Realization circularSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.ergosphere_forbids_static_observer.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.corotationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨corotationArena⟩
  objectArena := .source ⟨corotationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source corotationArena ⟨corotationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize circularSignature
    (fun _ p Ω => circularNorm p.1 p.2.1 p.2.2.1 p.2.2.2 Ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev ergoSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def ergoActual : Realization ergoSignature :=
  realize ergoSignature (fun _ p θ => rErgo p.1 p.2 θ) (fun e => nomatch e)

def ergoErased : Realization ergoSignature :=
  realize ergoSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev ergoArena : Arena where
  signature := ergoSignature
  Law R := ∀ {M a : ℝ}, |a| ≤ M → ∀ θ : ℝ,
    rPlus M a ≤ R.readout () ⟨M, a⟩ θ ∧
      (a ≠ 0 → (rPlus M a < rErgo M a θ ↔ Real.sin θ ≠ 0))

private theorem ergo_erasure_loses_separation : ¬ ergoArena.Law ergoErased := by
  intro h
  have he := (h (M := 1) (a := 1) (by norm_num) 0).1
  change rPlus 1 1 ≤ 0 at he
  norm_num [rPlus] at he

def ergoFamily : Registration ergoArena (type_of% (@ergosphere_strictly_outside_horizon)) where
  actual := ergoActual
  bridge := Iff.rfl
  variation := ⟨@ergosphere_strictly_outside_horizon, ergoErased, ergo_erasure_loses_separation⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    ergoArena.Law ergoActual ergoErased ergo_erasure_loses_separation
  dependence := by
    intro _
    refine ⟨⟨1, 1⟩, 0, Real.pi / 2, ?_⟩
    change rErgo 1 1 0 ≠ rErgo 1 1 (Real.pi / 2)
    norm_num [rErgo, Real.cos_pi_div_two]

abbrev staticSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def staticActual : Realization staticSignature :=
  realize staticSignature (fun _ p θ => g_tt p.1 p.2.1 p.2.2 θ) (fun e => nomatch e)

def staticErased : Realization staticSignature :=
  realize staticSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev staticArena : Arena where
  signature := staticSignature
  Law R := ∀ {M a r θ : ℝ}, 0 < M → rPlus M a < r → r < rErgo M a θ →
    0 < R.readout () ⟨M, a, r⟩ θ

private theorem static_erasure_loses_spacelike_norm : ¬ staticArena.Law staticErased := by
  intro h
  have hp : rPlus 1 1 < 3 / 2 := by norm_num [rPlus]
  have he : (3 / 2 : ℝ) < rErgo 1 1 (Real.pi / 2) := by norm_num [rErgo, Real.cos_pi_div_two]
  exact (lt_irrefl (0 : ℝ)) (h (by norm_num) hp he)

def staticFamily : Registration staticArena (type_of% (@g_tt_positive_in_ergosphere)) where
  actual := staticActual
  bridge := Iff.rfl
  variation := ⟨@g_tt_positive_in_ergosphere, staticErased, static_erasure_loses_spacelike_norm⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    staticArena.Law staticActual staticErased static_erasure_loses_spacelike_norm
  dependence := by
    intro _
    refine ⟨⟨1, 1, 3 / 2⟩, Real.pi / 3, Real.pi / 2, ?_⟩
    change g_tt 1 1 (3 / 2) (Real.pi / 3) ≠ g_tt 1 1 (3 / 2) (Real.pi / 2)
    norm_num [g_tt, kerrSigma, Real.cos_pi_div_three, Real.cos_pi_div_two]

def backwardHorizon : Realization rigiditySignature :=
  realize rigiditySignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev extractionArena : Arena where
  signature := rigiditySignature
  Law R := ∀ {M a E₀ Eout Ein Lin : ℝ}, 0 < a → a ≤ M →
    0 ≤ Ein - R.readout () M a * Lin → Ein < 0 → E₀ = Eout + Ein → Lin < 0 ∧ E₀ < Eout

private theorem backward_horizon_loses_retrograde_capture :
    ¬ extractionArena.Law backwardHorizon := by
  intro h
  have hf : 0 ≤ (-1 : ℝ) - backwardHorizon.readout () 1 1 * 1 := by
    change 0 ≤ (-1 : ℝ) - (-1) * 1
    norm_num
  have he := (h (E₀ := 0) (Eout := 1) (by norm_num) le_rfl hf (by norm_num)
    (by norm_num)).1
  norm_num at he

def extractionFamily : Registration extractionArena
    (type_of% (@penrose_extraction_forces_retrograde)) where
  actual := rigidityActual
  bridge := Iff.rfl
  variation := ⟨@penrose_extraction_forces_retrograde, backwardHorizon,
    backward_horizon_loses_retrograde_capture⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    extractionArena.Law rigidityActual backwardHorizon backward_horizon_loses_retrograde_capture
  dependence := rigidityFamily.dependence

def ergoRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ergosphere_strictly_outside_horizon) (Realization ergoSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.ergosphere_strictly_outside_horizon.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.ergoFamily
  realizationSource := none
  generated := false
  arena := .source ⟨ergoArena⟩
  objectArena := .source ⟨ergoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ergoArena ⟨ergoFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ergoSignature
    (fun _ p θ => rErgo p.1 p.2 θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def staticRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@g_tt_positive_in_ergosphere) (Realization staticSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.g_tt_positive_in_ergosphere.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.staticFamily
  realizationSource := none
  generated := false
  arena := .source ⟨staticArena⟩
  objectArena := .source ⟨staticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source staticArena ⟨staticFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize staticSignature
    (fun _ p θ => g_tt p.1 p.2.1 p.2.2 θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def extractionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@penrose_extraction_forces_retrograde) (Realization rigiditySignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.penrose_extraction_forces_retrograde.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D.extractionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨extractionArena⟩
  objectArena := .source ⟨extractionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source extractionArena ⟨extractionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rigiditySignature
    (fun _ M a => horizonOmega M a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
