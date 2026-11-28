import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
open _root_.D5.S3.Geometry.Lorentz.SL2CLorentzCover4D (V4 minkowskiNormSq)
open LeanInformationAudit
open Matrix

namespace Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion

set_option autoImplicit false

noncomputable section

private abbrev OneReadout (P X Y : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature P (fun _ => X) (fun _ => Y)

private def timeVector (t : ℝ) : V4 := ![t, 0, 0, 0]

@[simp] private theorem timeVector_normSq (t : ℝ) : minkowskiNormSq (timeVector t) = t ^ 2 := by
  simp [minkowskiNormSq, timeVector]

@[simp] private theorem timeVector_pair (s t : ℝ) :
    minkowski (timeVector s) (timeVector t) = s * t := by
  simp [minkowski, _root_.D5.S3.Geometry.Lorentz.WeylNullScreen.minkowski, timeVector]

@[simp] private theorem timeVector_diff_normSq (s t : ℝ) :
    minkowskiNormSq (timeVector s - timeVector t) = (s - t) ^ 2 := by
  simp [timeVector, minkowskiNormSq, Pi.sub_apply]

@[simp] private theorem sctDenom_zero (x : V4) : sctDenom 0 x = 1 := by
  simp [sctDenom, minkowski, _root_.D5.S3.Geometry.Lorentz.WeylNullScreen.minkowski, minkowskiNormSq]

abbrev involutionSignature := OneReadout Unit V4 V4

def involutionActual : Realization involutionSignature :=
  realize involutionSignature (fun _ _ x => conformalInv (conformalInv x)) (fun e => nomatch e)

def involutionErased : Realization involutionSignature :=
  realize involutionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev involutionArena : Arena where
  signature := involutionSignature
  Law R := ∀ x : V4, minkowskiNormSq x ≠ 0 →
    R.readout () () x = x ∧
      minkowskiNormSq (conformalInv x) = (minkowskiNormSq x)⁻¹

private theorem involution_erasure_fails : ¬ involutionArena.Law involutionErased := by
  intro h
  have he : (0 : V4) = timeVector 1 := (h (timeVector 1) (by norm_num)).1
  have h0 := congrFun he 0
  norm_num [timeVector] at h0

def involutionFamily : Registration involutionArena (type_of% (@conformalInv_involutive)) where
  actual := involutionActual
  bridge := Iff.rfl
  variation := ⟨conformalInv_involutive, involutionErased, involution_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    involutionArena.Law involutionActual involutionErased involution_erasure_fails
  dependence := by
    intro _
    refine ⟨(), timeVector 1, timeVector 2, ?_⟩
    change conformalInv (conformalInv (timeVector 1)) ≠ conformalInv (conformalInv (timeVector 2))
    rw [(conformalInv_involutive (timeVector 1) (by norm_num)).1,
      (conformalInv_involutive (timeVector 2) (by norm_num)).1]
    intro h
    have h0 := congrFun h 0
    norm_num [timeVector] at h0

abbrev inversionDistanceSignature := OneReadout V4 V4 ℝ

def inversionDistanceActual : Realization inversionDistanceSignature :=
  realize inversionDistanceSignature
    (fun _ p y => minkowskiNormSq (conformalInv p - conformalInv y)) (fun e => nomatch e)

def inversionDistanceErased : Realization inversionDistanceSignature :=
  realize inversionDistanceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev inversionDistanceArena : Arena where
  signature := inversionDistanceSignature
  Law R := ∀ (x y : V4), minkowskiNormSq x ≠ 0 → minkowskiNormSq y ≠ 0 →
    R.readout () x y = minkowskiNormSq (x - y) / (minkowskiNormSq x * minkowskiNormSq y)

private theorem inversion_distance_erasure_fails :
    ¬ inversionDistanceArena.Law inversionDistanceErased := by
  intro h
  have he : (0 : ℝ) =
      minkowskiNormSq (timeVector 1 - timeVector 2) /
        (minkowskiNormSq (timeVector 1) * minkowskiNormSq (timeVector 2)) :=
    h (timeVector 1) (timeVector 2) (by norm_num) (by norm_num)
  norm_num at he

def inversionDistanceFamily : Registration inversionDistanceArena
    (type_of% (@conformalInv_diff_normSq)) where
  actual := inversionDistanceActual
  bridge := Iff.rfl
  variation := ⟨conformalInv_diff_normSq, inversionDistanceErased, inversion_distance_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    inversionDistanceArena.Law inversionDistanceActual inversionDistanceErased
      inversion_distance_erasure_fails
  dependence := by
    intro _
    refine ⟨timeVector 1, timeVector 1, timeVector 2, ?_⟩
    change minkowskiNormSq (conformalInv (timeVector 1) - conformalInv (timeVector 1)) ≠
      minkowskiNormSq (conformalInv (timeVector 1) - conformalInv (timeVector 2))
    rw [conformalInv_diff_normSq _ _ (by norm_num) (by norm_num),
      conformalInv_diff_normSq _ _ (by norm_num) (by norm_num)]
    norm_num [minkowskiNormSq, timeVector]

abbrev derivativeSignature := OneReadout Unit V4 (V4 →L[ℝ] V4)

def derivativeActual : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ x => invDeriv x) (fun e => nomatch e)

def derivativeErased : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev derivativeArena : Arena where
  signature := derivativeSignature
  Law R := ∀ x : V4, minkowskiNormSq x ≠ 0 →
    HasFDerivAt conformalInv (R.readout () () x) x

private theorem derivative_erasure_fails : ¬ derivativeArena.Law derivativeErased := by
  intro h
  have hzero : HasFDerivAt conformalInv 0 (timeVector 1) := h (timeVector 1) (by norm_num)
  have he := (conformalInv_hasFDerivAt (timeVector 1) (by norm_num)).unique hzero
  have hp := conformalInv_metric_pullback (timeVector 1) (timeVector 1) (timeVector 1) (by norm_num)
  rw [he] at hp
  norm_num [minkowski, _root_.D5.S3.Geometry.Lorentz.WeylNullScreen.minkowski, timeVector, minkowskiNormSq] at hp

def derivativeFamily : Registration derivativeArena (type_of% (@conformalInv_hasFDerivAt)) where
  actual := derivativeActual
  bridge := Iff.rfl
  variation := ⟨conformalInv_hasFDerivAt, derivativeErased, derivative_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    derivativeArena.Law derivativeActual derivativeErased derivative_erasure_fails
  dependence := by
    intro _
    refine ⟨(), timeVector 1, timeVector 2, ?_⟩
    change invDeriv (timeVector 1) ≠ invDeriv (timeVector 2)
    intro he
    have h1 := conformalInv_metric_pullback (timeVector 1) (timeVector 1) (timeVector 1) (by norm_num)
    have h2 := conformalInv_metric_pullback (timeVector 2) (timeVector 1) (timeVector 1) (by norm_num)
    rw [he, h2] at h1
    norm_num at h1

abbrev metricPullbackSignature := OneReadout (Σ _ : V4, V4) V4 ℝ

def metricPullbackActual : Realization metricPullbackSignature :=
  realize metricPullbackSignature
    (fun _ p w => minkowski (invDeriv p.1 p.2) (invDeriv p.1 w)) (fun e => nomatch e)

def metricPullbackErased : Realization metricPullbackSignature :=
  realize metricPullbackSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev metricPullbackArena : Arena where
  signature := metricPullbackSignature
  Law R := ∀ x v w : V4, minkowskiNormSq x ≠ 0 →
    R.readout () ⟨x, v⟩ w = minkowskiNormSq x ^ (-2 : ℤ) * minkowski v w

private theorem metric_pullback_erasure_fails : ¬ metricPullbackArena.Law metricPullbackErased := by
  intro h
  have he : (0 : ℝ) = minkowskiNormSq (timeVector 1) ^ (-2 : ℤ) *
      minkowski (timeVector 1) (timeVector 1) :=
    h (timeVector 1) (timeVector 1) (timeVector 1) (by norm_num)
  norm_num at he

def metricPullbackFamily : Registration metricPullbackArena
    (type_of% (@conformalInv_metric_pullback)) where
  actual := metricPullbackActual
  bridge := Iff.rfl
  variation := ⟨conformalInv_metric_pullback, metricPullbackErased, metric_pullback_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    metricPullbackArena.Law metricPullbackActual metricPullbackErased metric_pullback_erasure_fails
  dependence := by
    intro _
    refine ⟨⟨timeVector 1, timeVector 1⟩, timeVector 1, timeVector 2, ?_⟩
    change minkowski (invDeriv (timeVector 1) (timeVector 1)) (invDeriv (timeVector 1) (timeVector 1)) ≠
      minkowski (invDeriv (timeVector 1) (timeVector 1)) (invDeriv (timeVector 1) (timeVector 2))
    rw [conformalInv_metric_pullback _ _ _ (by norm_num), conformalInv_metric_pullback _ _ _ (by norm_num)]
    norm_num

abbrev sctFormulaSignature := OneReadout V4 V4 V4

def sctFormulaActual : Realization sctFormulaSignature :=
  realize sctFormulaSignature (fun _ p x => sct p x) (fun e => nomatch e)

def sctFormulaErased : Realization sctFormulaSignature :=
  realize sctFormulaSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sctFormulaArena : Arena where
  signature := sctFormulaSignature
  Law R := ∀ b x : V4, minkowskiNormSq x ≠ 0 → sctDenom b x ≠ 0 →
    R.readout () b x = conformalInv (conformalInv x + b)

private theorem sct_formula_erasure_fails : ¬ sctFormulaArena.Law sctFormulaErased := by
  intro h
  have he : (0 : V4) = conformalInv (conformalInv (timeVector 1) + 0) :=
    h 0 (timeVector 1) (by norm_num) (by simp)
  rw [add_zero, (conformalInv_involutive (timeVector 1) (by norm_num)).1] at he
  have h0 := congrFun he 0
  norm_num [timeVector] at h0

def sctFormulaFamily : Registration sctFormulaArena (type_of% (@sct_explicit_formula)) where
  actual := sctFormulaActual
  bridge := Iff.rfl
  variation := ⟨sct_explicit_formula, sctFormulaErased, sct_formula_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sctFormulaArena.Law sctFormulaActual sctFormulaErased sct_formula_erasure_fails
  dependence := by
    intro _
    refine ⟨0, timeVector 1, timeVector 2, ?_⟩
    change sct 0 (timeVector 1) ≠ sct 0 (timeVector 2)
    intro h
    have h0 := congrFun h 0
    norm_num [sct, timeVector, Pi.smul_apply, Pi.add_apply] at h0

abbrev sctDistanceSignature := OneReadout (Σ _ : V4, V4) V4 ℝ

def sctDistanceActual : Realization sctDistanceSignature :=
  realize sctDistanceSignature
    (fun _ p y => minkowskiNormSq (sct p.1 p.2 - sct p.1 y)) (fun e => nomatch e)

def sctDistanceErased : Realization sctDistanceSignature :=
  realize sctDistanceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sctDistanceArena : Arena where
  signature := sctDistanceSignature
  Law R := ∀ b x y : V4, sctDenom b x ≠ 0 → sctDenom b y ≠ 0 →
    R.readout () ⟨b, x⟩ y =
      minkowskiNormSq (x - y) / (sctDenom b x * sctDenom b y)

private theorem sct_distance_erasure_fails : ¬ sctDistanceArena.Law sctDistanceErased := by
  intro h
  have he : (0 : ℝ) = minkowskiNormSq (timeVector 1 - timeVector 2) /
      (sctDenom 0 (timeVector 1) * sctDenom 0 (timeVector 2)) :=
    h 0 (timeVector 1) (timeVector 2) (by simp) (by simp)
  norm_num at he

def sctDistanceFamily : Registration sctDistanceArena (type_of% (@sct_diff_normSq)) where
  actual := sctDistanceActual
  bridge := Iff.rfl
  variation := ⟨sct_diff_normSq, sctDistanceErased, sct_distance_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sctDistanceArena.Law sctDistanceActual sctDistanceErased sct_distance_erasure_fails
  dependence := by
    intro _
    refine ⟨⟨0, timeVector 1⟩, timeVector 1, timeVector 2, ?_⟩
    change minkowskiNormSq (sct 0 (timeVector 1) - sct 0 (timeVector 1)) ≠
      minkowskiNormSq (sct 0 (timeVector 1) - sct 0 (timeVector 2))
    rw [sct_diff_normSq _ _ _ (by simp) (by simp), sct_diff_normSq _ _ _ (by simp) (by simp)]
    norm_num [minkowskiNormSq, timeVector]

abbrev crossRatioSignature := OneReadout Unit V4 (V4 → V4)

def crossRatioActual : Realization crossRatioSignature :=
  realize crossRatioSignature (fun _ _ b => sct b) (fun e => nomatch e)

def crossRatioErased : Realization crossRatioSignature :=
  realize crossRatioSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev crossRatioArena : Arena where
  signature := crossRatioSignature
  Law R := ∀ (x : Fin 4 → V4), minkowskiNormSq (x 0 - x 2) ≠ 0 →
    minkowskiNormSq (x 1 - x 3) ≠ 0 →
    (∀ a, PreservesCrossRatios (fun y => y + a) x) ∧
    (∀ Λ : Matrix (Fin 4) (Fin 4) ℝ,
      Λᵀ * _root_.D5.S3.Geometry.Lorentz.SL2CLorentzCover4D.eta * Λ =
        _root_.D5.S3.Geometry.Lorentz.SL2CLorentzCover4D.eta →
      PreservesCrossRatios (fun y => Λ *ᵥ y) x) ∧
    (∀ a : ℝ, a ≠ 0 → PreservesCrossRatios (fun y => a • y) x) ∧
    ((∀ i, minkowskiNormSq (x i) ≠ 0) → PreservesCrossRatios conformalInv x) ∧
    (∀ b, (∀ i, sctDenom b (x i) ≠ 0) → PreservesCrossRatios (R.readout () () b) x)

private theorem cross_ratio_erasure_fails : ¬ crossRatioArena.Law crossRatioErased := by
  intro h
  let x : Fin 4 → V4 := ![timeVector 1, timeVector 2, timeVector 3, timeVector 4]
  have h13 : minkowskiNormSq (x 0 - x 2) ≠ 0 := by norm_num [x]
  have h24 : minkowskiNormSq (x 1 - x 3) ≠ 0 := by norm_num [x]
  have he := ((h x h13 h24).2.2.2.2 0 (fun _ => by simp)).1
  exact he (by norm_num [crossRatioErased, realize, minkowskiNormSq])

def crossRatioFamily : Registration crossRatioArena
    (type_of% (@crossRatios_conformal_invariant)) where
  actual := crossRatioActual
  bridge := Iff.rfl
  variation := ⟨crossRatios_conformal_invariant, crossRatioErased, cross_ratio_erasure_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    crossRatioArena.Law crossRatioActual crossRatioErased cross_ratio_erasure_fails
  dependence := by
    intro _
    refine ⟨(), 0, timeVector 1, ?_⟩
    change sct 0 ≠ sct (timeVector 1)
    intro h
    have h0 := congrArg (fun f : V4 → V4 => f (timeVector 1) 0) h
    norm_num [sct, sctDenom, timeVector, minkowskiNormSq, minkowski,
      _root_.D5.S3.Geometry.Lorentz.WeylNullScreen.minkowski, Pi.smul_apply, Pi.add_apply] at h0

def involutionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformalInv_involutive) (Realization involutionSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.conformalInv_involutive.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.involutionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨involutionArena⟩
  objectArena := .source ⟨involutionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source involutionArena ⟨involutionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize involutionSignature
    (fun _ _ x => conformalInv (conformalInv x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def inversionDistanceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformalInv_diff_normSq) (Realization inversionDistanceSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.conformalInv_diff_normSq.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.inversionDistanceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨inversionDistanceArena⟩
  objectArena := .source ⟨inversionDistanceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inversionDistanceArena ⟨inversionDistanceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inversionDistanceSignature
    (fun _ p y => minkowskiNormSq (conformalInv p - conformalInv y)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def derivativeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformalInv_hasFDerivAt) (Realization derivativeSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.conformalInv_hasFDerivAt.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.derivativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨derivativeArena⟩
  objectArena := .source ⟨derivativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source derivativeArena ⟨derivativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature
    (fun _ _ x => invDeriv x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
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

def metricPullbackRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformalInv_metric_pullback) (Realization metricPullbackSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.conformalInv_metric_pullback.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.metricPullbackFamily
  realizationSource := none
  generated := false
  arena := .source ⟨metricPullbackArena⟩
  objectArena := .source ⟨metricPullbackArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source metricPullbackArena ⟨metricPullbackFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize metricPullbackSignature
    (fun _ p w => minkowski (invDeriv p.1 p.2) (invDeriv p.1 w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sctFormulaRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sct_explicit_formula) (Realization sctFormulaSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.sct_explicit_formula.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.sctFormulaFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sctFormulaArena⟩
  objectArena := .source ⟨sctFormulaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sctFormulaArena ⟨sctFormulaFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sctFormulaSignature
    (fun _ p x => sct p x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sctDistanceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sct_diff_normSq) (Realization sctDistanceSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.sct_diff_normSq.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.sctDistanceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sctDistanceArena⟩
  objectArena := .source ⟨sctDistanceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sctDistanceArena ⟨sctDistanceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sctDistanceSignature
    (fun _ p y => minkowskiNormSq (sct p.1 p.2 - sct p.1 y)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def crossRatioRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@crossRatios_conformal_invariant) (Realization crossRatioSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.crossRatios_conformal_invariant.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion.crossRatioFamily
  realizationSource := none
  generated := false
  arena := .source ⟨crossRatioArena⟩
  objectArena := .source ⟨crossRatioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source crossRatioArena ⟨crossRatioFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize crossRatioSignature
    (fun _ _ b => sct b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "body", "body",
        "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion
