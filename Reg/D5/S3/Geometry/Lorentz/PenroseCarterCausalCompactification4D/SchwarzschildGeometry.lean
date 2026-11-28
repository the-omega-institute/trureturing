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

namespace KruskalRegionIITrappingNoEscape

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => kruskalF x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ r => r) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M s dr du dv : ℝ} {r u v : ℝ → ℝ}
    (hM : 0 < M) (hr : 0 < r s) (hu0 : 0 < u s) (hv0 : 0 < v s)
    (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hsum : 0 < du + dv) (hd : HasDerivAt r dr s)
    (hu : HasDerivAt u du s) (hv : HasDerivAt v dv s)
    (he : ∀ᶠ x in nhds s, u x * v x = (obs.readout () ()) M (r x)),
    HasDerivAt (fun x => u x * v x) (du * v s + u s * dv) s ∧
      0 < du * v s + u s * dv ∧ dr < 0 ∧ r s < 2 * M

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (M := 1) (s := 0) (dr := 1) (du := 1) (dv := 0)
    (r := fun x => x + 1) (u := fun x => x + 1) (v := fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ((hasDerivAt_id 0).add_const 1) ((hasDerivAt_id 0).add_const 1)
    (hasDerivAt_const 0 1) (Filter.Eventually.of_forall (fun _ => by ring))
  norm_num at e

def family : Registration arena (type_of% (@kruskal_regionII_trapping_no_escape)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kruskal_regionII_trapping_no_escape, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change kruskalF (0) ≠ kruskalF (1)
    exact profile_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kruskal_regionII_trapping_no_escape) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskal_regionII_trapping_no_escape.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.KruskalRegionIITrappingNoEscape.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => kruskalF x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KruskalRegionIITrappingNoEscape

namespace KruskalSingularitySpacelike

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (fun x : ℝ => -x) x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {T X : ℝ → ℝ} {s dT dX : ℝ}
    (hT : HasDerivAt T dT s) (hX : HasDerivAt X dX s) (hn : dX ≠ 0)
    (he : ∀ᶠ x in nhds s, (T x) ^ 2 - (X x) ^ 2 = 1),
    (obs.readout () ()) (dT ^ 2) + dX ^ 2 = dX ^ 2 / (T s) ^ 2 ∧ 0 < -(dT ^ 2) + dX ^ 2

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (T := Real.cosh) (X := Real.sinh) (s := 0) (dT := 0) (dX := 1)
    (by simpa using Real.hasDerivAt_cosh 0) (by simpa using Real.hasDerivAt_sinh 0)
    (by norm_num) (Filter.Eventually.of_forall (fun x => by nlinarith [Real.cosh_sq x]))).1
  norm_num at e

def family : Registration arena (type_of% (@kruskal_singularity_spacelike)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kruskal_singularity_spacelike, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (fun x : ℝ => -x) (0) ≠ (fun x : ℝ => -x) (1)
    exact by norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kruskal_singularity_spacelike) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskal_singularity_spacelike.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.KruskalSingularitySpacelike.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (fun x : ℝ => -x) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KruskalSingularitySpacelike

namespace EinsteinRosenBridgeMinimalThroat

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => kruskalF x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => -1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M r U V : ℝ} (hM : 0 < M)
    (hT : (V + U) / 2 = 0) (he : U * V = (obs.readout () ()) M r),
    2 * M ≤ r ∧ (r = 2 * M ↔ (V - U) / 2 = 0)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (M := 1) (r := 0) (U := -1) (V := 1) (by norm_num)
    (by norm_num) (by norm_num)).1
  norm_num at e

def family : Registration arena (type_of% (@einstein_rosen_bridge_minimal_throat)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@einstein_rosen_bridge_minimal_throat, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change kruskalF (0) ≠ kruskalF (1)
    exact profile_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@einstein_rosen_bridge_minimal_throat) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.einstein_rosen_bridge_minimal_throat.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.EinsteinRosenBridgeMinimalThroat.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => kruskalF x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EinsteinRosenBridgeMinimalThroat

namespace SchwarzschildInteriorProperTimeBound

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => cycloidRadius x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M : ℝ} (hM : 0 < M),
    (∀ η, HasDerivAt ((obs.readout () ()) M) (-M * Real.sin η) η ∧
      HasDerivAt (cycloidTime M) (cycloidRadius M η) η) ∧
    (∀ η ∈ Set.Ioo 0 Real.pi,
      ((-M * Real.sin η) / cycloidRadius M η) ^ 2 = 2 * M / cycloidRadius M η - 1) ∧
    cycloidTime M Real.pi - cycloidTime M 0 = Real.pi * M ∧
    (∀ (τ dτ : ℝ → ℝ), ContinuousOn τ (Set.Icc 0 Real.pi) →
      (∀ η ∈ Set.Ioo 0 Real.pi, HasDerivAt τ (dτ η) η) →
      (∀ η ∈ Set.Ioo 0 Real.pi,
        dτ η ^ 2 * (2 * M / cycloidRadius M η - 1) ≤ (-M * Real.sin η) ^ 2) →
      τ Real.pi - τ 0 ≤ Real.pi * M)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := ((h (M := 1) (by norm_num)).1 (π / 2)).1
  have q := e.unique (hasDerivAt_const (π / 2) (0 : ℝ))
  norm_num at q

def family : Registration arena (type_of% (@schwarzschild_interior_proper_time_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@schwarzschild_interior_proper_time_bound, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change cycloidRadius (0) ≠ cycloidRadius (1)
    exact radius_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@schwarzschild_interior_proper_time_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.schwarzschild_interior_proper_time_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.SchwarzschildInteriorProperTimeBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => cycloidRadius x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg", "fn", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SchwarzschildInteriorProperTimeBound

namespace SchwarzschildInverseProperTimeDerivative

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => sqrt x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 2) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M r dr : ℝ}
    (hr : 0 < r) (hi : r < 2 * M)
    (hd : 2 * M / r - 1 ≤ dr ^ 2),
    |dr⁻¹| ≤ 1 / (obs.readout () ()) (2 * M / r - 1)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (M := 1) (r := 1) (dr := 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at e

def family : Registration arena (type_of% (@schwarzschild_inverse_proper_time_derivative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@schwarzschild_inverse_proper_time_derivative, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change sqrt (0) ≠ sqrt (1)
    exact by norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@schwarzschild_inverse_proper_time_derivative) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.schwarzschild_inverse_proper_time_derivative.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.SchwarzschildInverseProperTimeDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SchwarzschildInverseProperTimeDerivative

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
