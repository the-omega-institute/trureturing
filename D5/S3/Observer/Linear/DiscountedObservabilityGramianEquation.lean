/- GID: D5/S3/Observer/Linear/DiscountedObservabilityGramianEquation
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/DiscountedObservabilityGramianEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discounted observability Gramian satisfies its Lyapunov equation. -/

import D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity

/- Library-search audit trail (2026-08-25):
   * Exact family hits `discountedObservabilityGramian`,
     `discountedGramianTerm`, and `discounted_gramian_term_summable` supply the
     source operator series and its convergence; they are reused directly.
   * Exact pinned-Mathlib component hits `Summable.tsum_eq_zero_add`,
     `ContinuousLinearMap.adjoint_comp`, `ContinuousLinearMap.compL`, and
     `ContinuousLinearMap.map_tsum` supply the zeroth-term split, adjoint
     reversal, continuous sandwich map, and transport of the summable tail.
   * Repository and pinned-Mathlib searches found no exact theorem stating the
     discounted Gramian equation on this carrier. -/

namespace D5.S3.Observer.Linear.DiscountedObservabilityGramianEquation

open D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity
open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The convergent discounted observability series is the fixed point of the
associated discrete Lyapunov operator. -/
theorem discounted_observability_gramian_equation
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hconv : Real.sqrt β * ‖T.toContinuousLinearMap‖ < 1) :
    discountedObservabilityGramian T C β =
      (C.adjoint.comp C).toContinuousLinearMap +
        (β : 𝕜) •
          (T.adjoint.toContinuousLinearMap ∘L
            discountedObservabilityGramian T C β ∘L
            T.toContinuousLinearMap) := by
  have _hβ1 : β ≤ 1 := hβ1.le
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  let sandwich : (V →L[𝕜] V) →L[𝕜] (V →L[𝕜] V) :=
    (ContinuousLinearMap.compL 𝕜 V V V
      T.adjoint.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL 𝕜 V V V).flip T.toContinuousLinearMap)
  let weightedSandwich : (V →L[𝕜] V) →L[𝕜] (V →L[𝕜] V) :=
    (β : 𝕜) • sandwich
  have hsum := discounted_gramian_term_summable T C β hβ0 hconv
  have hzero : discountedGramianTerm T C β 0 =
      (C.adjoint.comp C).toContinuousLinearMap := by
    rw [discountedGramianTerm]
    simp only [pow_zero, RCLike.ofReal_one, one_smul]
    have hobserved : observedIterate T C 0 = C.toContinuousLinearMap := by
      ext x
      simp [observedIterate, LinearMap.comp_apply]
    rw [hobserved, ← LinearMap.adjoint_toContinuousLinearMap]
    rfl
  have hsucc : ∀ n : ℕ,
      discountedGramianTerm T C β (n + 1) =
        weightedSandwich (discountedGramianTerm T C β n) := by
    intro n
    have hobserved : observedIterate T C (n + 1) =
        observedIterate T C n ∘L T.toContinuousLinearMap := by
      ext x
      simp [observedIterate, pow_succ, LinearMap.comp_apply,
        Module.End.coe_pow]
    rw [discountedGramianTerm, discountedGramianTerm, hobserved,
      ContinuousLinearMap.adjoint_comp]
    simp [weightedSandwich, sandwich, pow_succ,
      LinearMap.adjoint_toContinuousLinearMap,
      ContinuousLinearMap.comp_assoc, smul_smul, mul_comm]
  have htail : (∑' n : ℕ, discountedGramianTerm T C β (n + 1)) =
      weightedSandwich (discountedObservabilityGramian T C β) := by
    rw [discountedObservabilityGramian, weightedSandwich.map_tsum hsum]
    exact tsum_congr hsucc
  calc
    discountedObservabilityGramian T C β =
        discountedGramianTerm T C β 0 +
          ∑' n : ℕ, discountedGramianTerm T C β (n + 1) :=
      hsum.tsum_eq_zero_add
    _ = (C.adjoint.comp C).toContinuousLinearMap +
        weightedSandwich (discountedObservabilityGramian T C β) := by
      rw [hzero, htail]
    _ = (C.adjoint.comp C).toContinuousLinearMap +
        (β : 𝕜) •
          (T.adjoint.toContinuousLinearMap ∘L
            discountedObservabilityGramian T C β ∘L
            T.toContinuousLinearMap) := by
      simp [weightedSandwich, sandwich]

#print axioms discounted_observability_gramian_equation

end D5.S3.Observer.Linear.DiscountedObservabilityGramianEquation
