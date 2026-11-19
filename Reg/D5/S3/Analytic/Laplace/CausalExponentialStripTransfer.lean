import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the transferred L² membership and kernel transform. -/

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform
open _root_.D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.CausalExponentialStripTransfer

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

namespace Membership

abbrev sig := signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ → ℂ)

def actual : Realization sig :=
  realize sig (fun _ _ g => g) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law R := ∀ {σ σ₀ C p : ℝ}, σ < σ₀ → 0 ≤ C → 0 < p →
    ∀ {F : ℂ → ℂ} {g : ℝ → ℂ},
      (∀ z : ℂ, z.re ∈ Icc σ σ₀ → DifferentiableAt ℂ F z) →
      (∀ a ∈ Icc σ σ₀, ∀ y : ℝ,
        ‖F ((a : ℂ) + y * Complex.I)‖ ≤ C * (1 + |y|) ^ (-p)) →
      Measurable g → (∀ᵐ t ∂(volume : Measure ℝ), ContinuousAt g t) →
      (∀ t < 0, g t = 0) → (∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Icc 0 T, ‖g t‖ ≤ M) →
      Integrable (tilt (σ₀ - σ) g) → 𝓕 (tilt (σ₀ - σ) g) = sectionAt F σ₀ →
      MemLp (sectionAt F σ) 2 → MemLp (R.readout () () g) 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have htilt : tilt (1 - 0) (0 : ℝ → ℂ) = 0 := by ext t; simp [tilt]
  have hsection (a : ℝ) : sectionAt (0 : ℂ → ℂ) a = 0 := rfl
  have hbad := h (σ := 0) (σ₀ := 1) (C := 0) (p := 1)
    (by norm_num) le_rfl (by norm_num) (F := 0) (g := 0)
    (fun _ _ => differentiableAt_const _)
    (by simp) measurable_zero (ae_of_all _ fun _ => continuousAt_const)
    (by simp) (fun _ => ⟨0, by simp⟩)
    (by rw [htilt]; exact integrable_zero ℝ ℂ volume)
    (by
      rw [htilt, hsection]
      funext ξ
      rw [Real.fourier_eq']
      simp)
    (by rw [hsection]; exact MemLp.zero)
  change MemLp (fun _ : ℝ => (1 : ℂ)) 2 at hbad
  rw [memLp_const_iff (by norm_num) (by simp)] at hbad
  simp at hbad

private theorem dependence : ObservationalDependence sig actual := by
  intro i
  refine ⟨(), 0, fun _ => 1, ?_⟩
  intro h
  exact zero_ne_one (congrFun h 0)

def family : Registration arena (type_of% @memLp_of_strip_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@memLp_of_strip_transfer, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@memLp_of_strip_transfer) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.CausalExponentialStripTransfer.memLp_of_strip_transfer.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.CausalExponentialStripTransfer.Membership.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ g => g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Membership

namespace KernelTransform

abbrev Params := Σ _ : ℝ, ℝ
abbrev sig := signature Params (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization sig :=
  realize sig (fun _ p ξ => multiplier p.1 p.2 ξ) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law R := ∀ (c : ℝ) {a : ℝ}, 0 < a → ∀ ξ : ℝ,
    𝓕 (kernel c a) ξ = R.readout () ⟨c, a⟩ ξ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (a := 1) (by norm_num) 0
  change 𝓕 (kernel 1 1) 0 = 0 at hbad
  rw [fourier_kernel 1 (by norm_num : (0 : ℝ) < 1)] at hbad
  norm_num [multiplier] at hbad

private theorem dependence : ObservationalDependence sig actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  change multiplier 1 1 0 ≠ multiplier 1 1 1
  intro h
  have hden : (1 : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  have hzero : multiplier 1 1 0 = 1 := by norm_num [multiplier]
  rw [hzero] at h
  have he : (1 : ℂ) / (1 + ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    simpa [multiplier] using h.symm
  have hi := congrArg Complex.im ((div_eq_iff hden).mp he)
  simp at hi

def family : Registration arena (type_of% @fourier_kernel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fourier_kernel, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fourier_kernel) (Realization sig) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.CausalExponentialStripTransfer.fourier_kernel.audit
  realizationName :=
    `Reg.D5.S3.Analytic.Laplace.CausalExponentialStripTransfer.KernelTransform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ p ξ => multiplier p.1 p.2 ξ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KernelTransform
end Reg.D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
