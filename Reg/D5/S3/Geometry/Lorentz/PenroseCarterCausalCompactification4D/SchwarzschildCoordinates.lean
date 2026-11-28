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

namespace KruskalFDerivAndStrictAnti

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => kruskalF x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M : ℝ} (hM : 0 < M),
    (∀ r, HasDerivAt (kruskalF M) (-r / (4 * M ^ 2) * Real.exp (r / (2 * M))) r) ∧
    StrictAntiOn ((obs.readout () ()) M) (Set.Ici 0) ∧ kruskalF M 0 = 1 ∧ kruskalF M (2 * M) = 0 ∧
    (∀ r ∈ Set.Ioo 0 (2 * M), kruskalF M r ∈ Set.Ioo 0 1) ∧
    (∀ r > 2 * M, kruskalF M r < 0) ∧
    Filter.Tendsto (kruskalF M) Filter.atTop Filter.atBot ∧
    Set.BijOn (kruskalF M) (Set.Ioi 0) (Set.Iio 1)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have ha : StrictAntiOn (fun _ : ℝ => (0 : ℝ)) (Set.Ici 0) :=
    (h (M := 1) (by norm_num)).2.1
  have e := ha (show (0 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num : (0 : ℝ) < 1)
  exact (lt_irrefl (0 : ℝ)) e

def family : Registration arena (type_of% (@kruskalF_deriv_and_strict_anti)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kruskalF_deriv_and_strict_anti, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change kruskalF (0) ≠ kruskalF (1)
    exact profile_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kruskalF_deriv_and_strict_anti) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskalF_deriv_and_strict_anti.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.KruskalFDerivAndStrictAnti.family
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
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KruskalFDerivAndStrictAnti

namespace KruskalUvProductAndRatio

abbrev signature : Signature := operandSignature (ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => U_ext x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) (t : ℝ),
    (obs.readout () ()) M t r < 0 ∧ 0 < V_ext M t r ∧ U_ext M t r * V_ext M t r = kruskalF M r ∧
    V_ext M t r / (-U_ext M t r) = Real.exp (t / (2 * M)) ∧
    2 * M * Real.log (V_ext M t r / (-U_ext M t r)) = t ∧
    U_ext M t r = -Real.exp ((rStar M r - t) / (4 * M)) ∧
    V_ext M t r = Real.exp ((rStar M r + t) / (4 * M))

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (M := 1) (r := 4) (by norm_num) (by norm_num) 0).1
  exact (lt_irrefl (0 : ℝ)) e

def family : Registration arena (type_of% (@kruskal_uv_product_and_ratio)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kruskal_uv_product_and_ratio, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change U_ext (0) ≠ U_ext (1)
    exact exterior_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kruskal_uv_product_and_ratio) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskal_uv_product_and_ratio.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.KruskalUvProductAndRatio.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => U_ext x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KruskalUvProductAndRatio

namespace KruskalMetricAnalyticPullback

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => kruskalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M s dt dr : ℝ} {t r : ℝ → ℝ}
    (hM : 0 < M) (hR : 2 * M < r s) (ht : HasDerivAt t dt s) (hr : HasDerivAt r dr s)
    (a : ℝ),
    -(1 - 2 * M / r s) * dt ^ 2 + (1 - 2 * M / r s)⁻¹ * dr ^ 2 + (r s) ^ 2 * a ^ 2 =
      -(obs.readout () ()) M (r s) * deriv (fun x => U_ext M (t x) (r x)) s *
        deriv (fun x => V_ext M (t x) (r x)) s + (r s) ^ 2 * a ^ 2

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (M := 1) (s := 0) (dt := 1) (dr := 0) (t := fun x => x)
    (r := fun _ => 4) (by norm_num) (by norm_num) (hasDerivAt_id 0)
    (hasDerivAt_const 0 4) 0
  norm_num at e

def family : Registration arena (type_of% (@kruskal_metric_analytic_pullback)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kruskal_metric_analytic_pullback, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change kruskalFactor (0) ≠ kruskalFactor (1)
    exact coefficient_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kruskal_metric_analytic_pullback) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskal_metric_analytic_pullback.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.KruskalMetricAnalyticPullback.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => kruskalFactor x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KruskalMetricAnalyticPullback

namespace KruskalHorizonNonsingular

abbrev signature : Signature := operandSignature (ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => kruskalFactor x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M : ℝ} (hM : 0 < M),
    (∀ r > 0, 0 < (obs.readout () ()) M r) ∧
    kruskalFactor M (2 * M) = 16 * M ^ 2 * Real.exp (-1) ∧
    BlackHoleThermodynamics4D.rPlus M 0 0 = 2 * M ∧
    (∀ q < 1, ∃ g : ℝ → ℝ, 0 < g q ∧ AnalyticAt ℝ g q ∧
      (∀ᶠ w in nhds q, kruskalF M (g w) = w) ∧
      AnalyticAt ℝ (fun w => kruskalFactor M (g w)) q)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (M := 1) (by norm_num)).1 1 (by norm_num)
  exact (lt_irrefl (0 : ℝ)) e

def family : Registration arena (type_of% (@kruskal_horizon_nonsingular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kruskal_horizon_nonsingular, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change kruskalFactor (0) ≠ kruskalFactor (1)
    exact coefficient_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kruskal_horizon_nonsingular) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.kruskal_horizon_nonsingular.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.KruskalHorizonNonsingular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => kruskalFactor x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KruskalHorizonNonsingular

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
