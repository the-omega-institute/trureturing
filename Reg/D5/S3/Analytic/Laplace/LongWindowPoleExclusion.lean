import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.LongWindowPoleExclusion
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.Laplace.LongWindowPoleExclusion
open _root_.D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter MeasureTheory
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Analytic.Laplace.LongWindowPoleExclusion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {g : ℝ → ℝ} {F : ℂ → ℂ}
    {Z : Set ℂ} {residue : ℂ → ℂ} {M θ δ C : ℝ},
    Measurable g → (∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2 * u)) →
    (∀ z : ℂ, 2 < z.re → laplace g z = F z) →
    (∀ z ∈ Z, z.re ≤ 1) →
    (∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) →
    (∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z) →
    (∀ ρ ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      F =ᶠ[𝓝[≠] ρ] fun z => residue ρ / (z - ρ) + H z) →
    (∀ ρ ∈ Z, residue ρ ≠ 0) →
    (∀ β : ℝ, (β : ℂ) ∈ Z → 0 < (residue (β : ℂ)).re) →
    0 ≤ θ → 0 < δ →
    (∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u)) →
    ∀ ρ : ℂ, V.readout () () Z ρ → ¬ θ < ρ.re

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  have h := @H (fun _ => 0) (fun _ => 0) ∅ (fun _ => 0) 0 ((1 : ℝ) / 2) 1 0
    measurable_const (by intro u hu; simp)
    (by intro z hz; simp [laplace])
    (by intro z hz; exact False.elim hz)
    (by intro z hz; exact Eventually.of_forall (fun _ => notMem_empty _))
    (by intro z hz hn; exact analyticAt_const)
    (by intro ρ hρ; exact False.elim hρ)
    (by intro ρ hρ; exact False.elim hρ)
    (by intro β hβ; exact False.elim hβ)
    (by norm_num) (by norm_num)
    (by intro U₀; exact ⟨U₀, le_rfl, fun u hu => by simp⟩)
    (1 : ℂ) True.intro
  exact h (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) ∈ (∅ : Set ℂ)) = ((0 : ℂ) ∈ Set.univ) at he
  simpa using he

def family : Registration arena (type_of% @long_window_pole_exclusion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@long_window_pole_exclusion, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@long_window_pole_exclusion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.LongWindowPoleExclusion.exclusionUnit
  realizationName := `Reg.D5.S3.Analytic.Laplace.LongWindowPoleExclusion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.LongWindowPoleExclusion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Estimate

def arena : Arena where
  signature := signature
  Law V := ∀ {g : ℝ → ℝ} {F : ℂ → ℂ}
    {Z : Set ℂ} {residue : ℂ → ℂ} {M θ δ C : ℝ},
    Measurable g → (∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2 * u)) →
    (∀ z : ℂ, 2 < z.re → laplace g z = F z) →
    (∀ z ∈ Z, z.re ≤ 1) →
    (∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) →
    (∀ z : ℂ, 0 < z.re → z ∉ Z → AnalyticAt ℂ F z) →
    (∀ ρ ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      F =ᶠ[𝓝[≠] ρ] fun z => residue ρ / (z - ρ) + H z) →
    (∀ ρ ∈ Z, residue ρ ≠ 0) →
    (∀ β : ℝ, (β : ℂ) ∈ Z → 0 < (residue (β : ℂ)).re) →
    0 ≤ θ → 0 < δ →
    (∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ C * Real.exp (θ * u)) →
    ∀ ρ : ℂ, V.readout () () Z ρ → θ < ρ.re →
    ∃ σ c d e B K : ℝ, 2 < σ ∧ θ < σ ∧
      0 < c ∧ 0 < d ∧ d < e ∧ e < σ - θ ∧ 0 ≤ B ∧ 0 ≤ K ∧
      ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ 1 ≤ U ∧
        let k := ⌊σ * ((2 + δ) / 2) * U⌋₊
        U ≤ k ∧ c / d ^ k ≤ B / e ^ k + K / (σ - θ) ^ k

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  obtain ⟨σ, c, d, e, B, K, _, _, hc, hd, hde, heE, _, hK, hestimate⟩ :=
    @H (fun _ => 0) (fun _ => 0) ∅ (fun _ => 0) 0 ((1 : ℝ) / 2) 1 0
      measurable_const (by intro u hu; simp)
      (by intro z hz; simp [laplace])
      (by intro z hz; exact False.elim hz)
      (by intro z hz; exact Eventually.of_forall (fun _ => notMem_empty _))
      (by intro z hz hn; exact analyticAt_const)
      (by intro ρ hρ; exact False.elim hρ)
      (by intro ρ hρ; exact False.elim hρ)
      (by intro β hβ; exact False.elim hβ)
      (by norm_num) (by norm_num)
      (by intro U₀; exact ⟨U₀, le_rfl, fun u hu => by simp⟩)
      (1 : ℂ) True.intro (by norm_num)
  apply _root_.D5.S3.Analytic.Laplace.LongWindowBounds.landau_window_contra
    (M := B) (C := K) hc hd hde (hde.trans heE)
  intro η hη U₀
  obtain ⟨U, hU, hUone, hk, hbound⟩ := hestimate U₀
  let k := ⌊σ * ((2 + (1 : ℝ)) / 2) * U⌋₊
  refine ⟨U, hU, k, hk, hbound.trans ?_⟩
  have hU0 : 0 ≤ U := by linarith
  have hE : 0 < σ - (1 : ℝ) / 2 := (hd.trans hde).trans heE
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have hratio := div_le_div_of_nonneg_right (le_mul_of_one_le_right hK hexp)
    (pow_nonneg hE.le k)
  dsimp [k] at hratio ⊢
  linarith

def family : Registration arena (type_of% @long_window_pole_estimate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@long_window_pole_estimate, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@long_window_pole_estimate) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.LongWindowPoleExclusion.estimateUnit
  realizationName := `Reg.D5.S3.Analytic.Laplace.LongWindowPoleExclusion.Estimate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.LongWindowPoleExclusion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Estimate

end Reg.D5.S3.Analytic.Laplace.LongWindowPoleExclusion
