/- GID: D5/S3/ResourceOrder/PayoffPricingFactorization
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/PayoffPricingFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Price factors through payoff range exactly when it kills null trades. -/

import Mathlib.LinearAlgebra.Isomorphisms

namespace D5.S3.ResourceOrder.PayoffPricingFactorization

/-- A linear price gives equal values to equal payoffs exactly when its kernel contains the
payoff kernel; equivalently, it factors uniquely through the attainable payoff range. -/
theorem payoff_price_factorization_iff
    {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (payoff : M →ₗ[R] N) (price : M →ₗ[R] R) :
    ((∀ z z', payoff z = payoff z' → price z = price z') ↔ payoff.ker ≤ price.ker) ∧
      (payoff.ker ≤ price.ker ↔
        ∃! factor : payoff.range →ₗ[R] R,
          ∀ z, price z = factor ⟨payoff z, payoff.mem_range_self z⟩) := by
  constructor
  · constructor
    · intro h z hz
      rw [LinearMap.mem_ker] at hz ⊢
      calc
        price z = price 0 := h z 0 (by simpa using hz)
        _ = 0 := price.map_zero
    · intro h z z' hpayoff
      have hsub : z - z' ∈ payoff.ker := by
        rw [LinearMap.mem_ker, map_sub, hpayoff, sub_self]
      have hprice := h hsub
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hprice
      exact hprice
  · constructor
    · intro hker
      let factor : payoff.range →ₗ[R] R :=
        (payoff.ker.liftQ price hker).comp payoff.quotKerEquivRange.symm.toLinearMap
      have hfactor : ∀ z, price z = factor ⟨payoff z, payoff.mem_range_self z⟩ := by
        intro z
        simp [factor]
      refine ⟨factor, hfactor, ?_⟩
      intro other hother
      apply LinearMap.ext
      intro y
      rcases y.property with ⟨z, hz⟩
      have hy : y = ⟨payoff z, payoff.mem_range_self z⟩ := Subtype.ext hz.symm
      rw [hy, ← hother z, ← hfactor z]
    · rintro ⟨factor, hfactor, _⟩
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      calc
        price z = factor ⟨payoff z, payoff.mem_range_self z⟩ := hfactor z
        _ = factor 0 := congrArg factor (Subtype.ext hz)
        _ = 0 := factor.map_zero

#print axioms payoff_price_factorization_iff

end D5.S3.ResourceOrder.PayoffPricingFactorization
