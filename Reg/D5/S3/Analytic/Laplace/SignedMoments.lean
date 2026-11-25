import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.SignedMoments
import D5.S3.Analytic.Laplace.CriticalGammaWindow
import Reg.Support.SingleDependentReadout

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Topology
open _root_.D5.S3.Analytic.Laplace.SignedMoments
open _root_.D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

namespace Reg.D5.S3.Analytic.Laplace.SignedMoments

namespace Absolute

abbrev sig := signature Unit (fun _ => ℝ → ℝ) (fun _ => Set ℝ → Measure ℝ → Prop)

def actual : Realization sig :=
  realize sig (fun _ _ F S μ => IntegrableOn F S μ) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {h : ℝ → ℝ} {a σ : ℝ}, Measurable h →
    (∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0)) →
    a < σ → ∀ k : ℕ,
    V.readout () () (fun u => u ^ k * |h u| * Real.exp (-σ * u)) (Ici 0) volume

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  exact H (h := fun _ => 0) (a := 0) (σ := 1) measurable_const
    (by intro t ht; simp) zero_lt_one 0

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), ?_⟩
  intro H
  have he := congrFun (congrFun H (Ici (0 : ℝ))) volume
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (0 : ℝ)) := by
    change IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ici (0 : ℝ)) =
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (0 : ℝ)) at he
    rw [← he]
    simp
  simpa [integrableOn_const_iff, Real.volume_Ici] using hi

def family : Registration arena (type_of% @absolute_moment_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@absolute_moment_integrable, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@absolute_moment_integrable) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Laplace.SignedMoments.absolute_moment_integrable.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedMoments.Absolute.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.SignedMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Absolute

namespace ComplexMoment

abbrev sig := signature Unit (fun _ => ℝ → ℂ) (fun _ => Set ℝ → Measure ℝ → Prop)

def actual : Realization sig :=
  realize sig (fun _ _ F S μ => IntegrableOn F S μ) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {h : ℝ → ℝ} {a : ℝ} {z : ℂ}, Measurable h →
    (∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0)) →
    a < z.re → ∀ k : ℕ,
    V.readout () () (fun u : ℝ => (u : ℂ) ^ k * (h u : ℂ) *
      Complex.exp (-z * u)) (Ici 0) volume

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  exact H (h := fun _ => 0) (a := 0) (z := 1) measurable_const
    (by intro t ht; simp) (by norm_num) 0

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), (fun _ : ℝ => (1 : ℂ)), ?_⟩
  intro H
  have he := congrFun (congrFun H (Ici (0 : ℝ))) volume
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ici (0 : ℝ)) := by
    change IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Ici (0 : ℝ)) =
      IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ici (0 : ℝ)) at he
    rw [← he]
    simp
  simpa [integrableOn_const_iff, Real.volume_Ici] using hi

def family : Registration arena (type_of% @moment_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_integrable, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_integrable) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedMoments.moment_integrable.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedMoments.ComplexMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.SignedMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ComplexMoment

namespace Derivative

abbrev sig := signature Unit (fun _ => ℂ → ℂ) (fun _ => ℂ → ℂ → Prop)

def actual : Realization sig :=
  realize sig (fun _ _ F d z => HasDerivAt F d z) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {h : ℝ → ℝ} {a : ℝ} {z : ℂ}, Measurable h →
    (∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0)) →
    a < z.re → ∀ k : ℕ,
    V.readout () () (moment h k) (-moment h (k + 1) z) z

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  exact H (h := fun _ => 0) (a := 0) (z := 1) measurable_const
    (by intro t ht; simp) (by norm_num) 0

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z), ?_⟩
  intro H
  have he := congrFun (congrFun H 0) 0
  have hd : HasDerivAt (fun z : ℂ => z) 0 0 := by
    change HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 0 =
      HasDerivAt (fun z : ℂ => z) 0 0 at he
    rw [← he]
    exact hasDerivAt_const 0 0
  exact zero_ne_one (hd.unique (hasDerivAt_id 0))

def family : Registration arena (type_of% @moment_hasDerivAt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_hasDerivAt, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_hasDerivAt) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedMoments.moment_hasDerivAt.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedMoments.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.SignedMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivative

namespace Iterated

abbrev sig := signature (Σ _ : ℂ, ℕ) (fun _ => ℂ → ℂ) (fun _ => ℂ)

def actual : Realization sig :=
  realize sig (fun _ p F => iteratedDeriv p.2 F p.1) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {h : ℝ → ℝ} {a : ℝ} {z : ℂ}, Measurable h →
    (∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0)) →
    a < z.re → ∀ k : ℕ,
    V.readout () ⟨z, k⟩ (laplace h) = (-1 : ℂ) ^ k * moment h k z

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  have he := H (h := fun _ => 0) (a := 0) (z := 1) measurable_const
    (by intro t ht; simp) (by norm_num) 0
  norm_num [rejected, realize, moment] at he

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨⟨0, 0⟩, (fun _ : ℂ => (0 : ℂ)), (fun _ : ℂ => (1 : ℂ)), ?_⟩
  change iteratedDeriv 0 (fun _ : ℂ => (0 : ℂ)) 0 ≠
    iteratedDeriv 0 (fun _ : ℂ => (1 : ℂ)) 0
  simp

def family : Registration arena (type_of% @iteratedDeriv_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@iteratedDeriv_laplace, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iteratedDeriv_laplace) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedMoments.iteratedDeriv_laplace.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedMoments.Iterated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.SignedMoments
    definition := none
    coordinates := #[2, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Iterated

namespace RealCenter

abbrev sig := signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization sig := realize sig (fun _ _ z => z.re) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {h : ℝ → ℝ} {a σ : ℝ}, Measurable h →
    (∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0)) →
    a < σ → ∀ k : ℕ,
    V.readout () () (((-1 : ℂ) ^ k * iteratedDeriv k (laplace h) (σ : ℂ)) /
        (k.factorial : ℂ)) =
      (∫ u in Ici (0 : ℝ), u ^ k * h u * Real.exp (-σ * u)) / k.factorial

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  have hh := H (h := fun _ => 0) (a := 0) (σ := 1) measurable_const
    (by intro t ht; simp) zero_lt_one 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩

def family : Registration arena (type_of% @alternating_derivative_real) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@alternating_derivative_real, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@alternating_derivative_real) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedMoments.alternating_derivative_real.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedMoments.RealCenter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.SignedMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RealCenter

namespace PositiveBound

abbrev sig := signature (Σ _ : ℝ → ℝ, ℂ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization sig :=
  realize sig (fun _ p k => 2 * ∫ u in Ici (0 : ℝ),
    u ^ k * max (p.1 u) 0 * Real.exp (-p.2.re * u)) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {h : ℝ → ℝ} {z : ℂ} (k : ℕ),
    ‖moment h k z‖ + (∫ u in Ici (0 : ℝ),
      u ^ k * h u * Real.exp (-z.re * u)) ≤ V.readout () ⟨h, z⟩ k

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  have he := H (h := fun _ => 0) (z := 1) 0
  norm_num [rejected, realize, moment] at he

private theorem exp_integral : (∫ u in Ici (0 : ℝ), Real.exp (-u)) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (0 : ℝ)

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  have hm := _root_.D5.S3.Analytic.Laplace.CriticalGammaWindow.moment_integral
    2 (r := 1) zero_lt_one
  have hm2 : (∫ u in Ioi (0 : ℝ), u ^ 2 * Real.exp (-u) / 2) = 1 := by
    simpa [_root_.D5.S3.Analytic.Laplace.CriticalGammaWindow.moment] using hm
  rw [integral_div] at hm2
  have hi2 : (∫ u in Ici (0 : ℝ), u ^ 2 * Real.exp (-u)) = 2 := by
    rw [integral_Ici_eq_integral_Ioi]
    linarith
  refine ⟨⟨(fun _ : ℝ => (1 : ℝ)), 1⟩, 0, 2, ?_⟩
  change (2 * ∫ u in Ici (0 : ℝ), u ^ 0 * max (1 : ℝ) 0 *
      Real.exp (-(1 : ℂ).re * u)) ≠
    2 * ∫ u in Ici (0 : ℝ), u ^ 2 * max (1 : ℝ) 0 * Real.exp (-(1 : ℂ).re * u)
  simp [exp_integral, hi2]

def family : Registration arena (type_of% @moment_norm_add_real_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_norm_add_real_le, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_norm_add_real_le) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedMoments.moment_norm_add_real_le.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedMoments.PositiveBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.SignedMoments
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveBound

end Reg.D5.S3.Analytic.Laplace.SignedMoments
