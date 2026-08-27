/- GID: D5/S3/Observer/Linear/DiscountedObservabilityEnergyIdentity
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/DiscountedObservabilityEnergyIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Gramian quadratic form equals total discounted readout energy. -/

import D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity

/- Library-search audit trail (2026-08-27):
   * Repository searches found no public theorem stating the discounted
     observability energy identity. The Gramian-kernel module contains the
     same summation calculation only through a private helper.
   * The canonical repository constructions `discountedObservabilityGramian`,
     `discountedGramianTerm`, and `observedIterate` are imported rather than
     redeclared.
   * Exact pinned-Mathlib component hit
     `ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right` supplies the
     termwise identity; no packaged infinite-series energy theorem was found. -/

namespace D5.S3.Observer.Linear.DiscountedObservabilityEnergyIdentity

open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open DiscountedObservabilityGramianPositivity

/-- The quadratic form of the source-constructed discounted observability
Gramian is exactly the total discounted squared readout energy. -/
theorem discounted_observability_energy_identity
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ)
    (hβ0 : 0 < β)
    (hconv : Real.sqrt β * ‖T.toContinuousLinearMap‖ < 1)
    (x : V) :
    RCLike.re (inner 𝕜 x (discountedObservabilityGramian T C β x)) =
      ∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2 := by
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  have hsum := discounted_gramian_term_summable T C β hβ0 hconv
  have hterm : ∀ n : ℕ,
      RCLike.re (inner 𝕜 x (discountedGramianTerm T C β n x)) =
        β ^ n * ‖observedIterate T C n x‖ ^ 2 := by
    intro n
    rw [discountedGramianTerm]
    simp only [smul_apply, inner_smul_right, RCLike.mul_re, RCLike.ofReal_re,
      RCLike.ofReal_im, zero_mul, sub_zero]
    rw [← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  rw [discountedObservabilityGramian]
  change RCLike.re (inner 𝕜 x (((ContinuousLinearMap.apply 𝕜 V) x)
    (∑' n : ℕ, discountedGramianTerm T C β n))) =
      ∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2
  rw [((ContinuousLinearMap.apply 𝕜 V) x).map_tsum hsum]
  have happly := hsum.mapL ((ContinuousLinearMap.apply 𝕜 V) x)
  change RCLike.re ((innerSL 𝕜 x)
    (∑' n : ℕ, ((ContinuousLinearMap.apply 𝕜 V) x)
      (discountedGramianTerm T C β n))) =
        ∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2
  rw [(innerSL 𝕜 x).map_tsum happly]
  have hinner := happly.mapL (innerSL 𝕜 x)
  change RCLike.reCLM
    (∑' n : ℕ, (innerSL 𝕜 x) (((ContinuousLinearMap.apply 𝕜 V) x)
      (discountedGramianTerm T C β n))) =
        ∑' n : ℕ, β ^ n * ‖observedIterate T C n x‖ ^ 2
  rw [RCLike.reCLM.map_tsum hinner]
  exact tsum_congr hterm

#print axioms discounted_observability_energy_identity

end D5.S3.Observer.Linear.DiscountedObservabilityEnergyIdentity
