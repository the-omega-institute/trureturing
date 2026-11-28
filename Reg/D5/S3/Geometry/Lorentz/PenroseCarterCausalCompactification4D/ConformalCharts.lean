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

namespace MinkowskiConformalMetricPullback

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => inverseTime x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {T R : ℝ → ℝ} {s dT dR : ℝ}
    (ht : HasDerivAt T dT s) (hr : HasDerivAt R dR s) (h : diamond (T s) (R s)) (w : ℝ),
    -deriv (fun x => (obs.readout () ()) (T x) (R x)) s ^ 2 +
      deriv (fun x => inverseRadius (T x) (R x)) s ^ 2 + inverseRadius (T s) (R s) ^ 2 * w ^ 2 =
      (conformalFactor (T s) (R s))⁻¹ ^ 2 * (-dT ^ 2 + dR ^ 2 + sin (R s) ^ 2 * w ^ 2)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (T := fun x => x) (R := fun _ => 0) (s := 0) (dT := 1) (dR := 0)
    (hasDerivAt_id 0) (hasDerivAt_const 0 0) (by simp [diamond, Real.pi_pos]) 0
  norm_num [inverseRadius, conformalFactor] at e

def family : Registration arena (type_of% (@minkowski_conformal_metric_pullback)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_conformal_metric_pullback, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π / 2, ?_⟩
    change inverseTime (0) ≠ inverseTime (π / 2)
    exact inverseTime_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_conformal_metric_pullback) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_conformal_metric_pullback.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiConformalMetricPullback.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => inverseTime x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiConformalMetricPullback

namespace DesitterConformalMetricPullback

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => desitterOmega x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {η : ℝ → ℝ} {s dη ℓ : ℝ}
    (hℓ : 0 < ℓ) (hl : -(π / 2) < η s) (hu : η s < π / 2)
    (hη : HasDerivAt η dη s) (v : ℝ),
    let τ := fun x => ℓ * deSitterTime (η x);
    -deriv τ s ^ 2 + (ℓ * cosh (τ s / ℓ)) ^ 2 * v ^ 2 =
      ((obs.readout () ()) ℓ (η s))⁻¹ ^ 2 * (-dη ^ 2 + v ^ 2)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (η := fun _ => 0) (s := 0) (dη := 0) (ℓ := 1) (by norm_num)
    (by linarith [Real.pi_pos]) (by positivity) (hasDerivAt_const 0 0) 1
  norm_num [time_zero] at e

def family : Registration arena (type_of% (@desitter_conformal_metric_pullback)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@desitter_conformal_metric_pullback, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change desitterOmega (0) ≠ desitterOmega (1)
    exact omega_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@desitter_conformal_metric_pullback) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.desitter_conformal_metric_pullback.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DesitterConformalMetricPullback.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => desitterOmega x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DesitterConformalMetricPullback

namespace DesitterScriSpacelikeHypersurface

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => desitterOmega x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {ℓ : ℝ} (hℓ : 0 < ℓ) (e : Bool),
    let η := if e then π / 2 else -(π / 2)
    let n := if e then -1 / ℓ else 1 / ℓ
    (obs.readout () ()) ℓ η = 0 ∧ HasDerivAt (desitterOmega ℓ) n η ∧ -(n ^ 2) = -1 / ℓ ^ 2 ∧
      -1 / ℓ ^ 2 < 0

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (ℓ := 1) (by norm_num) true).1
  norm_num at e

def family : Registration arena (type_of% (@desitter_scri_spacelike_hypersurface)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@desitter_scri_spacelike_hypersurface, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change desitterOmega (0) ≠ desitterOmega (1)
    exact omega_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@desitter_scri_spacelike_hypersurface) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.desitter_scri_spacelike_hypersurface.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DesitterScriSpacelikeHypersurface.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => desitterOmega x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DesitterScriSpacelikeHypersurface

namespace DesitterCausalHorizonDichotomy

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => sphericalReachable x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ => False) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {η χ : ℝ} (hχ : 0 ≤ χ),
    (∃ lo hi, -(π / 2) < lo ∧ hi < π / 2 ∧
      (obs.readout () ()) lo 0 η χ ∧ sphericalReachable η χ hi 0) ↔ |η| + χ < π / 2

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  obtain ⟨lo, hi, hlo, hhi, hbad, _⟩ :=
    (h (η := 0) (χ := 0) (by norm_num)).2 (by simpa using half_pos Real.pi_pos)
  exact hbad

def family : Registration arena (type_of% (@desitter_causal_horizon_dichotomy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@desitter_causal_horizon_dichotomy, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change sphericalReachable (0) ≠ sphericalReachable (1)
    exact spherical_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@desitter_causal_horizon_dichotomy) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.desitter_causal_horizon_dichotomy.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DesitterCausalHorizonDichotomy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => sphericalReachable x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DesitterCausalHorizonDichotomy

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
