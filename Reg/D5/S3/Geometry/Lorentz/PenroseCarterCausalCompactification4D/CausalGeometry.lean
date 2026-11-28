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

namespace CausalAngularDisplacement

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => einsteinMetric x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ _ _ => -1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {χ θ φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hχ : ∀ s ∈ Icc a b, DifferentiableAt ℝ χ s)
    (hc : ∀ s ∈ Icc a b,
      (obs.readout () ()) (χ s) (θ s) 1 (deriv χ s) (deriv θ s) (deriv φ s) ≤ 0),
    |χ b - χ a| ≤ b - a

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (χ := fun x => 2 * x) (θ := fun _ => 0) (φ := fun _ => 0)
    (a := 0) (b := 1) (by norm_num) (fun _ _ => by fun_prop) (fun _ _ => by norm_num)
  norm_num at e

def family : Registration arena (type_of% (@causal_angular_displacement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@causal_angular_displacement, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π / 2, ?_⟩
    change einsteinMetric (0) ≠ einsteinMetric (π / 2)
    exact einsteinMetric_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@causal_angular_displacement) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.causal_angular_displacement.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.CausalAngularDisplacement.family
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
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "fn", "arg", "fn", "fn", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CausalAngularDisplacement

namespace RadialReachableIff

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => radialReachable x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ => False) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (η₀ χ₀ η₁ χ₁ : ℝ),
    (obs.readout () ()) η₀ χ₀ η₁ χ₁ ↔ |χ₁ - χ₀| ≤ η₁ - η₀

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h 0 0 0 0).2 (by norm_num)
  exact e

def family : Registration arena (type_of% (@radialReachable_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radialReachable_iff, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change radialReachable (0) ≠ radialReachable (1)
    exact radial_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radialReachable_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.radialReachable_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.RadialReachableIff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => radialReachable x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RadialReachableIff

namespace SphericalReachableIff

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => sphericalReachable x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ => False) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (η₀ χ₀ η₁ χ₁ : ℝ),
    (obs.readout () ()) η₀ χ₀ η₁ χ₁ ↔ |χ₁ - χ₀| ≤ η₁ - η₀

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h 0 0 0 0).2 (by norm_num)
  exact e

def family : Registration arena (type_of% (@sphericalReachable_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sphericalReachable_iff, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change sphericalReachable (0) ≠ sphericalReachable (1)
    exact spherical_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sphericalReachable_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.sphericalReachable_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.SphericalReachableIff.family
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
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SphericalReachableIff

namespace DeSitterCausalDiamond

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => sphericalReachable x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ _ => False) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {ηlo ηhi η χ : ℝ} (hχ : 0 ≤ χ),
    ((obs.readout () ()) ηlo 0 η χ ∧ sphericalReachable η χ ηhi 0) ↔
      χ ≤ min (η - ηlo) (ηhi - η)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (ηlo := 0) (ηhi := 0) (η := 0) (χ := 0) (by norm_num)).2 (by norm_num)
  exact e.1

def family : Registration arena (type_of% (@deSitter_causal_diamond)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_causal_diamond, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change sphericalReachable (0) ≠ sphericalReachable (1)
    exact spherical_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_causal_diamond) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_causal_diamond.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterCausalDiamond.family
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
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterCausalDiamond

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
