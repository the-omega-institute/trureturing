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

namespace MinkowskiCornerDerivatives

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun T _ => T) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {T R : ℝ → ℝ} {s dT dR : ℝ}
    (hT : HasDerivAt T dT s) (hR : HasDerivAt R dR s)
    (hc : (T s = π ∧ R s = 0) ∨ (T s = -π ∧ R s = 0) ∨
      (T s = 0 ∧ R s = π)),
    HasDerivAt (fun x => (obs.readout () ()) (T x) (R x)) 0 s

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (T := fun x => x) (R := fun _ => 0) (s := π) (dT := 1) (dR := 0)
    (hasDerivAt_id π) (hasDerivAt_const π 0) (Or.inl ⟨rfl, rfl⟩)
  have q := e.unique (hasDerivAt_id π)
  norm_num at q

def family : Registration arena (type_of% (@minkowski_corner_derivatives)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_corner_derivatives, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change conformalFactor (0) ≠ conformalFactor (π)
    exact factor_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_corner_derivatives) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_corner_derivatives.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiCornerDerivatives.family
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiCornerDerivatives

namespace MinkowskiBoundaryDerivatives

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => conformalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun T _ => T) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (R : ℝ),
    HasDerivAt (fun x : ℝ => π - x) (-1) R ∧
    HasDerivAt (fun x : ℝ => x - π) 1 R ∧
    HasDerivAt (fun x => (obs.readout () ()) (π - x) x) 0 R ∧
    HasDerivAt (fun x => conformalFactor (x - π) x) 0 R

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h 0).2.2.1
  have q := e.unique ((hasDerivAt_id (0 : ℝ)).const_sub π)
  norm_num at q

def family : Registration arena (type_of% (@minkowski_boundary_derivatives)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_boundary_derivatives, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change conformalFactor (0) ≠ conformalFactor (π)
    exact factor_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_boundary_derivatives) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_boundary_derivatives.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiBoundaryDerivatives.family
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
      path := #["body", "arg", "arg", "fn", "arg", "fn", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiBoundaryDerivatives

namespace MinkowskiCornerLimits

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => minkowskiT x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := Tendsto (fun t : ℝ => ((obs.readout () ()) t 0, minkowskiR t 0)) atTop (𝓝 (π, 0)) ∧
    Tendsto (fun t : ℝ => (minkowskiT t 0, minkowskiR t 0)) atBot (𝓝 (-π, 0)) ∧
    Tendsto (fun r : ℝ => (minkowskiT 0 r, minkowskiR 0 r)) atTop (𝓝 (0, π))

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (continuous_fst.tendsto (π, (0 : ℝ))).comp h.1
  have q := tendsto_nhds_unique e (tendsto_const_nhds (x := (0 : ℝ)))
  exact Real.pi_ne_zero q

def family : Registration arena (type_of% (@minkowski_corner_limits)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minkowski_corner_limits, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change minkowskiT (0) ≠ minkowskiT (1)
    exact minkowskiT_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@minkowski_corner_limits) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.minkowski_corner_limits.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiCornerLimits.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => minkowskiT x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiCornerLimits

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
