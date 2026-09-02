/- GID: D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A symmetric simple zero remains reflection-fixed along its local continuation. -/

import D5.S3.Zeros.Symmetry.SimpleZeroNoBifurcation

namespace D5.S3.Zeros.Symmetry.SymmetricSimpleZeroFixedAxis

open Filter
open D5.S3.Weil.Convention D5.S3.Weil.ReflectionLedger
open D5.S3.Zeros.Symmetry.SimpleZeroNoBifurcation
open scoped ComplexConjugate Topology

/-- A symmetric simple zero has a unique nearby implicit-function continuation.  The
continuation remains reflection-fixed and therefore stays on the critical axis. -/
theorem symmetric_simple_zero_fixed_axis
    (F : ℝ → ℂ → ℂ)
    (dτ : ℝ → ℂ → ℝ →L[ℝ] ℂ)
    (ds : ℝ → ℂ → ℂ)
    (τ₀ : ℝ) (s₀ : ℂ)
    (hreflection : ∀ τ s, F τ (mirror s) = conj (F τ s))
    (hτ : ∀ᶠ v in 𝓝 (τ₀, s₀),
      HasFDerivAt (fun τ => F τ v.2) (dτ v.1 v.2) v.1)
    (hs : ∀ᶠ v in 𝓝 (τ₀, s₀),
      HasDerivAt (F v.1) (ds v.1 v.2) v.2)
    (hτ_cont : ContinuousAt (Function.uncurry dτ) (τ₀, s₀))
    (hs_cont : ContinuousAt
      (fun v : ℝ × ℂ => (ds v.1 v.2) • (1 : ℂ →L[ℝ] ℂ)) (τ₀, s₀))
    (hzero : F τ₀ s₀ = 0)
    (hsimple : ds τ₀ s₀ ≠ 0)
    (hfixed : mirror s₀ = s₀) :
    ∃ δ > 0, ∃ ε > 0, ∃ ρ : ℝ → ℂ,
      ρ τ₀ = s₀ ∧
      ContinuousAt ρ τ₀ ∧
      (∀ κ, |κ - τ₀| < δ → ρ κ ∈ Metric.ball s₀ ε) ∧
      (∀ κ, |κ - τ₀| < δ → F κ (ρ κ) = 0) ∧
      (∀ κ, |κ - τ₀| < δ → ∀ s, s ∈ Metric.ball s₀ ε →
        F κ s = 0 → s = ρ κ) ∧
      (∀ κ, |κ - τ₀| < δ → mirror (ρ κ) = ρ κ) ∧
      ∀ κ, |κ - τ₀| < δ → (ρ κ).re = criticalAbscissa := by
  have hs_real : ∀ᶠ v in 𝓝 (τ₀, s₀),
      HasFDerivAt (F v.1) ((ds v.1 v.2) • (1 : ℂ →L[ℝ] ℂ)) v.2 := by
    filter_upwards [hs] with v hv
    exact hv.complexToReal_fderiv
  let derivativeEquiv : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (ds τ₀ s₀) hsimple)
  have hinvertible :
      (((ds τ₀ s₀) • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ).IsInvertible := by
    change ((derivativeEquiv : ℂ →L[ℝ] ℂ)).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
  let branch : ℝ → ℂ :=
    implicitFunctionOfBivariate
      (f := F) (f₁ := dτ)
      (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
      hτ hs_real hτ_cont hs_cont hinvertible
  have hbranch_tendsto : Tendsto branch (𝓝 τ₀) (𝓝 s₀) := by
    exact tendsto_implicitFunctionOfBivariate
      (f := F) (f₁ := dτ)
      (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
      hτ hs_real hτ_cont hs_cont hinvertible
  have hbranch_zero : ∀ᶠ κ in 𝓝 τ₀, F κ (branch κ) = 0 := by
    simpa [branch, hzero] using
      eventually_apply_implicitFunctionOfBivariate
        (f := F) (f₁ := dτ)
        (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
        hτ hs_real hτ_cont hs_cont hinvertible
  have hunique :=
    eventually_apply_eq_iff_implicitFunctionOfBivariate
      (f := F) (f₁ := dτ)
      (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
      hτ hs_real hτ_cont hs_cont hinvertible
  have hbranch_base : branch τ₀ = s₀ := hunique.self_of_nhds.mp rfl
  have hbranch_cont : ContinuousAt branch τ₀ := by
    change Tendsto branch (𝓝 τ₀) (𝓝 (branch τ₀))
    rw [hbranch_base]
    exact hbranch_tendsto
  have hunique_zero : ∀ᶠ v in 𝓝 (τ₀, s₀),
      F v.1 v.2 = 0 ↔ branch v.1 = v.2 := by
    simpa only [hzero] using hunique
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hunique_zero
  let ε : ℝ := r / 2
  have hε : 0 < ε := by
    dsimp [ε]
    exact half_pos hr
  have hεr : ε < r := by
    dsimp [ε]
    linarith
  have hbranch_near : ∀ᶠ κ in 𝓝 τ₀, branch κ ∈ Metric.ball s₀ ε :=
    hbranch_tendsto.eventually (Metric.ball_mem_nhds s₀ hε)
  have hmirror_tendsto : Tendsto (fun κ => mirror (branch κ)) (𝓝 τ₀) (𝓝 s₀) := by
    have hmirror_cont : Continuous mirror := by
      exact continuous_const.sub Complex.continuous_conj
    have htendsto := (hmirror_cont.tendsto s₀).comp hbranch_tendsto
    rw [hfixed] at htendsto
    change Tendsto (mirror ∘ branch) (𝓝 τ₀) (𝓝 s₀)
    exact htendsto
  have hmirror_near : ∀ᶠ κ in 𝓝 τ₀,
      mirror (branch κ) ∈ Metric.ball s₀ ε :=
    hmirror_tendsto.eventually (Metric.ball_mem_nhds s₀ hε)
  have hparameter : ∀ᶠ κ in 𝓝 τ₀,
      F κ (branch κ) = 0 ∧
      branch κ ∈ Metric.ball s₀ ε ∧
      mirror (branch κ) ∈ Metric.ball s₀ ε := by
    filter_upwards [hbranch_zero, hbranch_near, hmirror_near] with κ hzeroκ hnear hmirrorNear
    exact ⟨hzeroκ, hnear, hmirrorNear⟩
  obtain ⟨δ₀, hδ₀, hδ₀ball⟩ := Metric.mem_nhds_iff.mp hparameter
  let δ : ℝ := min δ₀ ε
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₀ hε
  have hδ_le_δ₀ : δ ≤ δ₀ := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_ε : δ ≤ ε := by
    dsimp [δ]
    exact min_le_right _ _
  have hparameter_of (κ : ℝ) (hκ : |κ - τ₀| < δ) :
      F κ (branch κ) = 0 ∧
      branch κ ∈ Metric.ball s₀ ε ∧
      mirror (branch κ) ∈ Metric.ball s₀ ε := by
    apply hδ₀ball
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_lt_of_le hκ hδ_le_δ₀
  have hpair_mem (κ : ℝ) (hκ : |κ - τ₀| < δ) (s : ℂ)
      (hsball : s ∈ Metric.ball s₀ ε) :
      (κ, s) ∈ Metric.ball (τ₀, s₀) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq]
      exact lt_trans (lt_of_lt_of_le hκ hδ_le_ε) hεr
    · exact lt_trans (Metric.mem_ball.mp hsball) hεr
  have hpair_iff (κ : ℝ) (hκ : |κ - τ₀| < δ) (s : ℂ)
      (hsball : s ∈ Metric.ball s₀ ε) :
      F κ s = 0 ↔ branch κ = s :=
    hball (hpair_mem κ hκ s hsball)
  have hbranch_fixed (κ : ℝ) (hκ : |κ - τ₀| < δ) :
      mirror (branch κ) = branch κ := by
    have hdata := hparameter_of κ hκ
    have hmirror_zero : F κ (mirror (branch κ)) = 0 := by
      simp [hreflection κ (branch κ), hdata.1]
    exact ((hpair_iff κ hκ (mirror (branch κ)) hdata.2.2).mp hmirror_zero).symm
  refine ⟨δ, hδ, ε, hε, branch, hbranch_base, hbranch_cont, ?_, ?_, ?_, ?_, ?_⟩
  · intro κ hκ
    exact (hparameter_of κ hκ).2.1
  · intro κ hκ
    exact (hparameter_of κ hκ).1
  · intro κ hκ s hsball hzeros
    exact ((hpair_iff κ hκ s hsball).mp hzeros).symm
  · intro κ hκ
    exact hbranch_fixed κ hκ
  · intro κ hκ
    exact mirror_fixed_re_eq (branch κ) (hbranch_fixed κ hκ)

#print axioms symmetric_simple_zero_fixed_axis

end D5.S3.Zeros.Symmetry.SymmetricSimpleZeroFixedAxis
