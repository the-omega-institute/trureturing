import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.SignedWindowMoments
import Reg.Support.SingleDependentReadout

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Real Filter
open scoped Topology
open _root_.D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)
open _root_.D5.S3.Analytic.Laplace.SignedWindowMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

namespace Reg.D5.S3.Analytic.Laplace.SignedWindowMoments

namespace Growth

abbrev sig := signature Unit (fun _ => ℝ → ℝ) (fun _ => Set ℝ → Measure ℝ → Prop)
def actual : Realization sig :=
  realize sig (fun _ _ f S μ => IntegrableOn f S μ) (fun e => nomatch e)
def rejected : Realization sig :=
  realize sig (fun _ _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {g : ℝ → ℝ} {M σ : ℝ}, Measurable g →
    (∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u)) → 2 < σ →
    V.readout () () (fun u => g u * exp (-σ * u)) (Ici 0) volume

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  exact H (g := fun _ => 0) (M := 0) (σ := 3) measurable_const
    (by simp) (by norm_num)

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), ?_⟩
  intro H
  have he := congrFun (congrFun H (Ici (0 : ℝ))) volume
  change IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ici (0 : ℝ)) =
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (0 : ℝ)) at he
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (0 : ℝ)) := by
    rw [← he]
    simp
  simpa [integrableOn_const_iff, Real.volume_Ici] using hi

def family : Registration arena (type_of% @growth_convergence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@growth_convergence, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@growth_convergence) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedWindowMoments.growth_convergence.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedWindowMoments.Growth.family
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
    owner := `D5.S3.Analytic.Laplace.SignedWindowMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

namespace FixedWindow

abbrev sig := signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization sig := realize sig (fun _ _ M => M) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {g : ℝ → ℝ} {M σ θ C U h b : ℝ}, Measurable g →
    (∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u)) →
    0 ≤ θ → θ < σ → 1 < h → h < b →
    2 < σ * (1 - h / b) →
    0 ≤ σ * (h * log h - h + 1) - 2 →
    0 ≤ σ * (b - h - h * log (b / h)) - 2 * b →
    0 < U → (∀ u ∈ Icc U (b * U), g u ≤ C * exp (θ * u)) →
    ∀ z : ℂ, z.re = σ →
    let k := ⌊σ * h * U⌋₊
    (‖iteratedDeriv k (laplace g) z‖ +
        ∫ u in Ici (0 : ℝ), u ^ k * g u * exp (-σ * u)) / k.factorial ≤
      (2 * (|C| / (σ - θ) + V.readout () () M * (1 / σ + b / (h * σ)))) *
        (σ - θ)⁻¹ ^ k

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  obtain ⟨σ, ⟨hsign, hL, hR⟩, hσ⟩ :=
    (((_root_.D5.S3.Analytic.Laplace.CriticalGammaWindow.adjustable_window_off_mass
      (h := 2) (b := 3) (by norm_num) (by norm_num)).1 0).and
      (eventually_gt_atTop (2 : ℝ))).exists
  have hθσ : (1 : ℝ) < σ := by linarith
  have hh := H (g := fun _ => 0) (M := 0) (σ := σ) (θ := 1)
    (C := 0) (U := 1) (h := 2) (b := 3) measurable_const (by simp)
    zero_le_one hθσ (by norm_num) (by norm_num) hsign hL.le hR.le
    zero_lt_one (by simp) (σ : ℂ) rfl
  have he : laplace (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext z
    simp [laplace]
  rw [he] at hh
  simp only [iteratedDeriv_fun_const_zero, norm_zero, mul_zero, zero_mul, integral_zero,
    add_zero, zero_div, abs_zero, zero_add, rejected, realize] at hh
  have hσ0 : 0 < σ := by linarith
  have hp : 0 < 2 * (1 / σ + 3 / (2 * σ)) *
      (σ - 1)⁻¹ ^ ⌊σ * 2 * 1⌋₊ := by positivity
  nlinarith

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩

def family : Registration arena (type_of% @moment_bound_on_window) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_bound_on_window, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_bound_on_window) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedWindowMoments.moment_bound_on_window.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedWindowMoments.FixedWindow.family
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
    owner := `D5.S3.Analytic.Laplace.SignedWindowMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedWindow

namespace LongWindow

abbrev sig := signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization sig :=
  realize sig (fun _ _ K => K) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {g : ℝ → ℝ} {M θ C b : ℝ}, Measurable g →
    (∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u)) → 0 ≤ θ → 1 < b →
    ∃ σ K : ℝ, 2 < σ ∧ θ < σ ∧ 0 ≤ K ∧
      ∀ U : ℝ, 1 ≤ U →
      (∀ u ∈ Icc U (b * U), g u ≤ C * exp (θ * u)) →
      let k := ⌊σ * ((1 + b) / 2) * U⌋₊
      U ≤ k ∧ ∀ z : ℂ, z.re = σ →
        (‖iteratedDeriv k (laplace g) z‖ +
            ∫ u in Ici (0 : ℝ), u ^ k * g u * exp (-σ * u)) / k.factorial ≤
          V.readout () () K * (σ - θ)⁻¹ ^ k

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  obtain ⟨σ, K, hσ, hθσ, hK, hb⟩ := H (g := fun _ => 0) (M := 0)
    (θ := 1) (C := 0) (b := 2) measurable_const (by simp) zero_le_one (by norm_num)
  obtain ⟨hk, hbound⟩ := hb 1 le_rfl (by simp)
  have hh := hbound (σ : ℂ) rfl
  let k := ⌊σ * ((1 + (2 : ℝ)) / 2) * 1⌋₊
  have hp : 0 < (σ - 1)⁻¹ ^ k := pow_pos (inv_pos.mpr (by linarith)) k
  change (‖iteratedDeriv k (laplace (fun _ : ℝ => (0 : ℝ))) (σ : ℂ)‖ + _) / _ ≤ _ at hh
  have he : laplace (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext z
    simp [laplace]
  rw [he] at hh
  simp [rejected, realize] at hh
  exact (not_le_of_gt (pow_pos (sub_pos.mpr hθσ) _)) hh

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩

def family : Registration arena (type_of% @long_window_moment_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@long_window_moment_bound, rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@long_window_moment_bound) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.SignedWindowMoments.long_window_moment_bound.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.SignedWindowMoments.LongWindow.family
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
    owner := `D5.S3.Analytic.Laplace.SignedWindowMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body",
        "body", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LongWindow

end Reg.D5.S3.Analytic.Laplace.SignedWindowMoments
