import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.Common

/-! Complete source laws with single function-operand interventions. -/

open _root_.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz
open LeanInformationAudit Real Set Filter
open scoped Topology

namespace Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MinkowskiMetricPullback

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => minkowskiMetric x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (t r θ dt dr dθ dφ : ℝ),
    conformalFactor (minkowskiT t r) (minkowskiR t r)^2 *
      (obs.readout () ()) r θ dt dr dθ dφ =
    cylinderMetric (minkowskiR t r) θ
      ((dt + dr) / (1 + (t + r)^2) + (dt - dr) / (1 + (t - r)^2))
      ((dt + dr) / (1 + (t + r)^2) - (dt - dr) / (1 + (t - r)^2)) dθ dφ

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h 0 0 0 1 0 0 0
  norm_num [minkowskiR, cylinderMetric, angularSpeedSq] at e

def family : Registration arena (type_of% (@minkowski_metric_pullback)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_metric_pullback, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change minkowskiMetric (0) ≠ minkowskiMetric (1)
    exact minkowskiMetric_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_metric_pullback) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_metric_pullback.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiMetricPullback.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => minkowskiMetric x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiMetricPullback

namespace MinkowskiCurvePullback

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => minkowskiMetric x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {t r θ φ : ℝ → ℝ} {s dt dr dθ dφ : ℝ}
    (ht : HasDerivAt t dt s) (hr : HasDerivAt r dr s)
    (hθ : HasDerivAt θ dθ s) (hφ : HasDerivAt φ dφ s),
    conformalFactor (minkowskiT (t s) (r s)) (minkowskiR (t s) (r s))^2 *
      (obs.readout () ()) (r s) (θ s) dt dr dθ dφ =
    cylinderMetric (minkowskiR (t s) (r s)) (θ s)
      (deriv (fun x => minkowskiT (t x) (r x)) s)
      (deriv (fun x => minkowskiR (t x) (r x)) s) (deriv θ s) (deriv φ s)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (t := fun x => x) (r := fun _ => 0) (θ := fun _ => 0)
    (φ := fun _ => 0) (s := 0) (dt := 1) (dr := 0) (dθ := 0) (dφ := 0)
    (hasDerivAt_id 0) (hasDerivAt_const 0 0) (hasDerivAt_const 0 0) (hasDerivAt_const 0 0)
  have hd := (minkowski_coordinate_derivatives (hasDerivAt_id (0 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ)))
  have hT := hd.1.deriv
  have hR := hd.2.deriv
  simp only [id_eq] at hT hR
  rw [hT, hR, (hasDerivAt_const 0 (0 : ℝ)).deriv] at e
  norm_num [minkowskiR, cylinderMetric, angularSpeedSq] at e

def family : Registration arena (type_of% (@minkowski_curve_pullback)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_curve_pullback, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change minkowskiMetric (0) ≠ minkowskiMetric (1)
    exact minkowskiMetric_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_curve_pullback) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_curve_pullback.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiCurvePullback.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => minkowskiMetric x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiCurvePullback

namespace ConformalFactorDerivative

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun T _ => T) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {T R : ℝ → ℝ} {s dT dR : ℝ}
    (hT : HasDerivAt T dT s) (hR : HasDerivAt R dR s),
    HasDerivAt (fun x => (obs.readout () ()) (T x) (R x))
      (-sin (T s) * dT - sin (R s) * dR) s

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (T := fun x => x) (R := fun _ => 0) (s := 0) (dT := 1) (dR := 0)
    (hasDerivAt_id 0) (hasDerivAt_const 0 0)
  have q := e.unique (hasDerivAt_id 0)
  norm_num at q

def family : Registration arena (type_of% (@conformalFactor_derivative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conformalFactor_derivative, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change conformalFactor (0) ≠ conformalFactor (π)
    exact factor_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformalFactor_derivative) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.conformalFactor_derivative.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.ConformalFactorDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ConformalFactorDerivative

namespace MinkowskiNullBoundary

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (R : ℝ),
    (obs.readout () ()) (π - R) R = 0 ∧ conformalFactor (R - π) R = 0 ∧
    -(sin (π - R))^2 + sin R^2 = 0 ∧ -(sin (R - π))^2 + sin R^2 = 0

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h 0).1
  norm_num at e

def family : Registration arena (type_of% (@minkowski_null_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_null_boundary, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change conformalFactor (0) ≠ conformalFactor (π)
    exact factor_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_null_boundary) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_null_boundary.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiNullBoundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiNullBoundary

namespace MinkowskiBoundaryRegular

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => sin x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {R : ℝ} (hR : 0 < R) (hπ : R < π),
    -(obs.readout () ()) (π - R) ≠ 0 ∧ -sin (R - π) ≠ 0

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (R := π / 2) (by positivity) (by linarith [Real.pi_pos])).1
  exact e (by norm_num)

def family : Registration arena (type_of% (@minkowski_boundary_regular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_boundary_regular, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π / 2, ?_⟩
    change sin (0) ≠ sin (π / 2)
    exact sin_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_boundary_regular) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_boundary_regular.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiBoundaryRegular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiBoundaryRegular

namespace MinkowskiThreeCorners

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := (obs.readout () ()) π 0 = 0 ∧ conformalFactor (-π) 0 = 0 ∧ conformalFactor 0 π = 0 ∧
    sin π = 0 ∧ sin (-π) = 0 ∧ sin (0 : ℝ) = 0

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h.1
  norm_num at e

def family : Registration arena (type_of% (@minkowski_three_corners)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_three_corners, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change conformalFactor (0) ≠ conformalFactor (π)
    exact factor_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_three_corners) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_three_corners.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiThreeCorners.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiThreeCorners

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
