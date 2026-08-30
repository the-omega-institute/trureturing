/- GID: D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/SimpleZeroNoBifurcation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection keeps simple critical zeros on-line; off-line birth requires multiplicity. -/

import D5.S3.Weil.ReflectionLedger
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

namespace D5.S3.Zeros.Symmetry.SimpleZeroNoBifurcation

open Filter
open D5.S3.Weil.Convention D5.S3.Weil.ReflectionLedger
open scoped ComplexConjugate Topology

/-- For a continuously differentiable real family of holomorphic functions, completed
reflection makes the unique branch through a simple critical-line zero reflection-fixed.
Consequently, a convergent sequence of off-line zeros can be born on the line only where
the function and its complex derivative both vanish. -/
theorem simple_zero_no_bifurcation
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
      (fun v : ℝ × ℂ => (ds v.1 v.2) • (1 : ℂ →L[ℝ] ℂ)) (τ₀, s₀)) :
    ((F τ₀ s₀ = 0 ∧ ds τ₀ s₀ ≠ 0 ∧ s₀.re = criticalAbscissa) →
      ∀ᶠ v in 𝓝 (τ₀, s₀), F v.1 v.2 = 0 → v.2.re = criticalAbscissa) ∧
    ((s₀.re = criticalAbscissa ∧
      ∃ τ : ℕ → ℝ, ∃ s : ℕ → ℂ,
        Tendsto τ atTop (𝓝 τ₀) ∧
        Tendsto s atTop (𝓝 s₀) ∧
        ∀ n, F (τ n) (s n) = 0 ∧ (s n).re ≠ criticalAbscissa) →
      F τ₀ s₀ = 0 ∧ ds τ₀ s₀ = 0) := by
  have hs_real : ∀ᶠ v in 𝓝 (τ₀, s₀),
      HasFDerivAt (F v.1) ((ds v.1 v.2) • (1 : ℂ →L[ℝ] ℂ)) v.2 := by
    filter_upwards [hs] with v hv
    exact hv.complexToReal_fderiv
  have hF_strict : HasStrictFDerivAt (Function.uncurry F)
      ((dτ τ₀ s₀).coprod ((ds τ₀ s₀) • (1 : ℂ →L[ℝ] ℂ))) (τ₀, s₀) :=
    hasStrictFDerivAt_uncurry_coprod
      (f := F) (f₁ := dτ)
      (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
      hτ hs_real hτ_cont hs_cont
  have hF_cont : ContinuousAt (Function.uncurry F) (τ₀, s₀) := hF_strict.continuousAt
  have hno_bifurcation :
      (F τ₀ s₀ = 0 ∧ ds τ₀ s₀ ≠ 0 ∧ s₀.re = criticalAbscissa) →
        ∀ᶠ v in 𝓝 (τ₀, s₀), F v.1 v.2 = 0 → v.2.re = criticalAbscissa := by
    rintro ⟨hzero, hsimple, hcritical⟩
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
    have hbase_mirror : mirror s₀ = s₀ := by
      exact ((mirror_reversal_spec (Nat.castAddMonoidHom ℝ) s₀).2.2 hcritical).symm
    have hmirror_tendsto : Tendsto (fun τ => mirror (branch τ)) (𝓝 τ₀) (𝓝 s₀) := by
      have hmirror_cont : Continuous mirror := by
        exact continuous_const.sub Complex.continuous_conj
      have htendsto := (hmirror_cont.tendsto s₀).comp hbranch_tendsto
      rw [hbase_mirror] at htendsto
      change Tendsto (mirror ∘ branch) (𝓝 τ₀) (𝓝 s₀)
      exact htendsto
    have hpair_tendsto :
        Tendsto (fun τ => (τ, mirror (branch τ))) (𝓝 τ₀) (𝓝 (τ₀, s₀)) :=
      tendsto_id.prodMk_nhds hmirror_tendsto
    have hbranch_zero : ∀ᶠ τ in 𝓝 τ₀, F τ (branch τ) = 0 := by
      simpa [branch, hzero] using
        eventually_apply_implicitFunctionOfBivariate
          (f := F) (f₁ := dτ)
          (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
          hτ hs_real hτ_cont hs_cont hinvertible
    have hmirror_zero : ∀ᶠ τ in 𝓝 τ₀, F τ (mirror (branch τ)) = 0 := by
      filter_upwards [hbranch_zero] with τ hzeroτ
      simp [hreflection τ (branch τ), hzeroτ]
    have hunique :=
      eventually_apply_eq_iff_implicitFunctionOfBivariate
        (f := F) (f₁ := dτ)
        (f₂ := fun τ s => (ds τ s) • (1 : ℂ →L[ℝ] ℂ))
        hτ hs_real hτ_cont hs_cont hinvertible
    have hbranch_fixed : ∀ᶠ τ in 𝓝 τ₀, mirror (branch τ) = branch τ := by
      filter_upwards [hmirror_zero, hpair_tendsto.eventually hunique] with τ hmirrorZero hiff
      exact (hiff.mp (hmirrorZero.trans hzero.symm)).symm
    filter_upwards [hunique, continuousAt_fst.eventually hbranch_fixed] with v hiff hfixed hvzero
    have hbranch_eq : branch v.1 = v.2 := hiff.mp (hvzero.trans hzero.symm)
    apply mirror_fixed_re_eq v.2
    simpa [hbranch_eq] using hfixed
  refine ⟨hno_bifurcation, ?_⟩
  rintro ⟨hcritical, τ, s, hτ_tendsto, hs_tendsto, hzeros⟩
  have hpair_tendsto : Tendsto (fun n => (τ n, s n)) atTop (𝓝 (τ₀, s₀)) :=
    hτ_tendsto.prodMk_nhds hs_tendsto
  have hbase_zero : F τ₀ s₀ = 0 := by
    apply tendsto_nhds_unique (hF_cont.tendsto.comp hpair_tendsto)
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (hzeros n).1.symm)
  refine ⟨hbase_zero, ?_⟩
  by_contra hsimple
  have hlocal := hno_bifurcation ⟨hbase_zero, hsimple, hcritical⟩
  have hlocal_sequence :
      ∀ᶠ n in atTop, F (τ n) (s n) = 0 → (s n).re = criticalAbscissa :=
    hpair_tendsto.eventually hlocal
  have heventually_line : ∀ᶠ n in atTop, (s n).re = criticalAbscissa := by
    filter_upwards [hlocal_sequence] with n hn
    exact hn (hzeros n).1
  obtain ⟨n, hn⟩ := heventually_line.exists
  exact (hzeros n).2 hn

#print axioms simple_zero_no_bifurcation

end D5.S3.Zeros.Symmetry.SimpleZeroNoBifurcation
