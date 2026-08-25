/- GID: D5/S3/Observer/Linear/DiscountedObservabilityGramianKernel
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/DiscountedObservabilityGramianKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discounted observability Gramian kernel is the all-future readout kernel. -/

import D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity
import D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace

/- Library-search audit trail (2026-08-25):
   * Repository searches found no existing theorem identifying the kernel of
     the discounted observability Gramian.
   * Exact repository hit `MaximalUnobservableSubspace` supplies the canonical
     all-future readout-kernel carrier; this module imports it rather than
     declaring a sibling construction.
   * Exact pinned-Mathlib component hits
     `ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right` and
     `Summable.tsum_pos` supply the single-term energy identity and the strict
     positivity of a nonnegative summable series with a positive term. -/

namespace D5.S3.Observer.Linear.DiscountedObservabilityGramianKernel

open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open DiscountedObservabilityGramianPositivity

private theorem discounted_gramian_term_energy
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ) (n : ℕ) (x : V) :
    RCLike.re (inner 𝕜 x (discountedGramianTerm T C β n x)) =
      β ^ n * ‖observedIterate T C n x‖ ^ 2 := by
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  rw [discountedGramianTerm]
  simp only [smul_apply, inner_smul_right, RCLike.mul_re, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, sub_zero]
  rw [← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]

/-- Under the source's discount range and convergence premise, the kernel of
the discounted observability Gramian is exactly the canonical all-future
readout kernel. -/
theorem discounted_observability_gramian_kernel
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hconv : Real.sqrt β * ‖T.toContinuousLinearMap‖ < 1) :
    LinearMap.ker (discountedObservabilityGramian T C β).toLinearMap =
      ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k)) := by
  have _hβ1 : β ≤ 1 := hβ1.le
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  have hsum := discounted_gramian_term_summable T C β hβ0 hconv
  apply le_antisymm
  · intro x hx
    have hgramian : discountedObservabilityGramian T C β x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have henergySummable : Summable (fun n : ℕ =>
        β ^ n * ‖observedIterate T C n x‖ ^ 2) := by
      have happly := hsum.mapL ((ContinuousLinearMap.apply 𝕜 V) x)
      have hinner := happly.mapL (innerSL 𝕜 x)
      have hre := hinner.mapL RCLike.reCLM
      change Summable (fun n : ℕ =>
        RCLike.re (inner 𝕜 x (discountedGramianTerm T C β n x))) at hre
      simpa only [discounted_gramian_term_energy] using hre
    have henergyZero : (∑' n : ℕ,
        β ^ n * ‖observedIterate T C n x‖ ^ 2) = 0 := by
      calc
        (∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2) =
            RCLike.re (inner 𝕜 x (discountedObservabilityGramian T C β x)) := by
          rw [discountedObservabilityGramian]
          change (∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2) =
            RCLike.re (inner 𝕜 x (((ContinuousLinearMap.apply 𝕜 V) x)
              (∑' n : ℕ, discountedGramianTerm T C β n)))
          rw [((ContinuousLinearMap.apply 𝕜 V) x).map_tsum hsum]
          have happly := hsum.mapL ((ContinuousLinearMap.apply 𝕜 V) x)
          change (∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2) =
            RCLike.re ((innerSL 𝕜 x)
              (∑' n : ℕ, ((ContinuousLinearMap.apply 𝕜 V) x)
                (discountedGramianTerm T C β n)))
          rw [(innerSL 𝕜 x).map_tsum happly]
          have hinner := happly.mapL (innerSL 𝕜 x)
          change (∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2) =
            RCLike.reCLM
              (∑' n : ℕ, (innerSL 𝕜 x) (((ContinuousLinearMap.apply 𝕜 V) x)
                (discountedGramianTerm T C β n)))
          rw [RCLike.reCLM.map_tsum hinner]
          congr 1
          funext n
          exact (discounted_gramian_term_energy T C β n x).symm
        _ = 0 := by simp [hgramian]
    apply (Submodule.mem_iInf _).mpr
    intro k
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    by_contra hk
    have htermPos : 0 < β ^ k * ‖observedIterate T C k x‖ ^ 2 :=
      mul_pos (pow_pos hβ0 k) (sq_pos_of_pos (norm_pos_iff.mpr hk))
    have htotalPos : 0 < ∑' n : ℕ,
        β ^ n * ‖observedIterate T C n x‖ ^ 2 :=
      henergySummable.tsum_pos
        (fun n => mul_nonneg (pow_nonneg hβ0.le n) (sq_nonneg _)) k htermPos
    exact htotalPos.ne henergyZero.symm
  · intro x hx
    rw [LinearMap.mem_ker]
    change discountedObservabilityGramian T C β x = 0
    rw [discountedObservabilityGramian]
    change ((ContinuousLinearMap.apply 𝕜 V) x)
      (∑' n : ℕ, discountedGramianTerm T C β n) = 0
    rw [((ContinuousLinearMap.apply 𝕜 V) x).map_tsum hsum]
    have hterm : ∀ n : ℕ, discountedGramianTerm T C β n x = 0 := by
      intro n
      have hfuture := (Submodule.mem_iInf _).mp hx n
      have hobserved : observedIterate T C n x = 0 := by
        simpa [observedIterate, LinearMap.mem_ker, LinearMap.comp_apply] using hfuture
      rw [discountedGramianTerm]
      simp [hobserved]
    calc
      (∑' n : ℕ, discountedGramianTerm T C β n x) =
          ∑' _n : ℕ, (0 : V) := tsum_congr hterm
      _ = 0 := tsum_zero

#print axioms discounted_observability_gramian_kernel

end D5.S3.Observer.Linear.DiscountedObservabilityGramianKernel
