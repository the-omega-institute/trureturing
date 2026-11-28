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

namespace DeSitterWeightedMetricPullback

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterMetric x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ _ _ _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {t χ θ φ : ℝ → ℝ} {s α dt dχ dθ dφ : ℝ}
    (ht : HasDerivAt t dt s) (hχ : HasDerivAt χ dχ s)
    (hθ : HasDerivAt θ dθ s) (hφ : HasDerivAt φ dφ s),
    cos (deSitterEta (t s))^2 * (obs.readout () ()) α (t s) (χ s) dt dχ dθ dφ (θ s) =
      α^2 * einsteinMetric (χ s) (θ s) (deriv (fun x => deSitterEta (t x)) s)
        (deriv χ s) (deriv θ s) (deriv φ s)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (t := fun x => x) (χ := fun _ => 0) (θ := fun _ => 0)
    (φ := fun _ => 0) (s := 0) (α := 1) (dt := 1) (dχ := 0) (dθ := 0) (dφ := 0)
    (hasDerivAt_id 0) (hasDerivAt_const 0 0) (hasDerivAt_const 0 0) (hasDerivAt_const 0 0)
  rw [(deSitterEta_derivative 0).deriv, (hasDerivAt_const 0 (0 : ℝ)).deriv] at e
  have hc : cos (deSitterEta 0) = 1 := by simpa using deSitter_cos_cosh 0
  norm_num [einsteinMetric, angularSpeedSq, hc] at e

def family : Registration arena (type_of% (@deSitter_weighted_metric_pullback)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_weighted_metric_pullback, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterMetric (0) ≠ deSitterMetric (1)
    exact deSitterMetric_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_weighted_metric_pullback) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_weighted_metric_pullback.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterWeightedMetricPullback.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterMetric x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "fn", "fn", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterWeightedMetricPullback

namespace DeSitterSpacelikeBoundary

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => cos x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := (obs.readout () ()) (π / 2) = 0 ∧ cos (-(π / 2)) = 0 ∧
    -(sin (π / 2))^2 = -1 ∧ -(sin (-(π / 2)))^2 = -1 ∧
    HasDerivAt cos (-1) (π / 2) ∧ HasDerivAt cos 1 (-(π / 2))

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h.1
  norm_num at e

def family : Registration arena (type_of% (@deSitter_spacelike_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_spacelike_boundary, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change cos (0) ≠ cos (π)
    exact cos_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_spacelike_boundary) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_spacelike_boundary.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterSpacelikeBoundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => cos x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterSpacelikeBoundary

namespace DeSitterBoundaryInducedPositive

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => einsteinMetric x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {χ θ dχ dθ dφ : ℝ}
    (hχ : sin χ ≠ 0) (hθ : sin θ ≠ 0) (hv : dχ ≠ 0 ∨ dθ ≠ 0 ∨ dφ ≠ 0),
    0 < (obs.readout () ()) χ θ 0 dχ dθ dφ

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (χ := π / 2) (θ := π / 2) (dχ := 1) (dθ := 0) (dφ := 0)
    (by norm_num) (by norm_num) (Or.inl (by norm_num))
  exact (lt_irrefl (0 : ℝ)) e

def family : Registration arena (type_of% (@deSitter_boundary_induced_positive)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_boundary_induced_positive, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π / 2, ?_⟩
    change einsteinMetric (0) ≠ einsteinMetric (π / 2)
    exact einsteinMetric_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_boundary_induced_positive) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_boundary_induced_positive.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterBoundaryInducedPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => einsteinMetric x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterBoundaryInducedPositive

namespace DeSitterBoundaryLimits

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := Tendsto (obs.readout () ()) atTop (𝓝 (π / 2)) ∧
    Tendsto deSitterEta atBot (𝓝 (-(π / 2)))

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have q := tendsto_nhds_unique h.1 (tendsto_const_nhds (x := (0 : ℝ)))
  linarith [Real.pi_pos]

def family : Registration arena (type_of% (@deSitter_boundary_limits)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_boundary_limits, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterEta (0) ≠ deSitterEta (1)
    exact eta_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_boundary_limits) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_boundary_limits.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterBoundaryLimits.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterBoundaryLimits

namespace DeSitterScaleDerivative

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterScale x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {α : ℝ} (hα : 0 < α) (τ : ℝ),
    HasDerivAt ((obs.readout () ()) α) (sinh (τ / α)) τ

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (α := 1) (by norm_num) 1).unique (hasDerivAt_const 1 (0 : ℝ))
  norm_num at e

def family : Registration arena (type_of% (@deSitterScale_derivative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitterScale_derivative, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterScale (0) ≠ deSitterScale (1)
    exact scale_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitterScale_derivative) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitterScale_derivative.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterScaleDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterScale x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterScaleDerivative

namespace DeSitterFriedmann

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterScale x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ τ => exp τ) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {α : ℝ} (hα : 0 < α) (τ : ℝ),
    FLRWCosmologyFriedmann4D.hubble ((obs.readout () ()) α) τ = sinh (τ / α) / deSitterScale α τ ∧
    FLRWCosmologyFriedmann4D.hubble (deSitterScale α) τ ^ 2 +
      1 / deSitterScale α τ ^ 2 = 1 / α^2

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (α := 1) (by norm_num) 0).1
  norm_num [FLRWCosmologyFriedmann4D.hubble, Real.deriv_exp, deSitterScale] at e

def family : Registration arena (type_of% (@deSitter_friedmann)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_friedmann, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterScale (0) ≠ deSitterScale (1)
    exact scale_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_friedmann) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_friedmann.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterFriedmann.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterScale x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterFriedmann

namespace DeSitterConformalFactorPos

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => cos x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {η : ℝ} (hη : -(π / 2) < η) (hπ : η < π / 2),
    0 < (obs.readout () ()) η

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (η := 0) (by linarith [Real.pi_pos]) (by positivity)
  exact (lt_irrefl (0 : ℝ)) e

def family : Registration arena (type_of% (@deSitter_conformalFactor_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_conformalFactor_pos, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change cos (0) ≠ cos (π)
    exact cos_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_conformalFactor_pos) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_conformalFactor_pos.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterConformalFactorPos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => cos x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterConformalFactorPos

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
