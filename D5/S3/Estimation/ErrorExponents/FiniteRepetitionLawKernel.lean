/- GID: D5/S3/Estimation/ErrorExponents/FiniteRepetitionLawKernel
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/FiniteRepetitionLawKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite repetition amplifies affinity without separating equal laws. -/

/- Library-search audit trail (2026-08-26):
   * Repository searches for finite repetition, equality of repeated laws, product-law kernels,
     and affinity amplification found no existing theorem exposing both source clauses.
   * The frozen `iidPower` is the canonical finite independent-product law;
     `bhattacharyya_iidPower_multiplicative` supplies exact affinity multiplication, and
     `iid_power_sum_one` supplies the marginal-recovery normalization step.
   * Pinned Mathlib provides `pow_lt_self_of_lt_one₀`, finite product sums, and function
     extensionality, but no exact statistical theorem combining amplification with equality
     reflection for positive finite product powers.
-/

import D5.S3.Estimation.BhattacharyyaExponent

namespace D5.S3.Estimation.ErrorExponents.FiniteRepetitionLawKernel

open D5.S3.DivergenceSupport.PowerAdditivity
open D5.S3.Estimation.BhattacharyyaExponent
open D5.S3.RenyiDivergence
open D5.S3.TotalVariation.Bhattacharyya

/-- In the nonsaturated affinity regime, taking at least two independent copies strictly reduces
overlap. For every positive number of copies, equality of the repeated laws is equivalent to
equality of the one-shot laws, so repetition never crosses the one-shot law kernel. -/
theorem finite_repetition_amplifies_without_crossing_law_kernel
    {State Outcome : Type*} [Fintype Outcome]
    (law : State -> Outcome -> Real) (x y : State) (n : Nat)
    (hx : (forall i, 0 <= law x i) ∧ ∑ i, law x i = 1)
    (hy : (forall i, 0 <= law y i) ∧ ∑ i, law y i = 1)
    (hn : 0 < n) :
    ((1 < n ∧ 0 < bhattacharyya (law x) (law y) ∧
        bhattacharyya (law x) (law y) < 1) ->
      bhattacharyya (iidPower (law x) n) (iidPower (law y) n) <
        bhattacharyya (law x) (law y)) ∧
    (iidPower (law x) n = iidPower (law y) n ↔ law x = law y) := by
  classical
  constructor
  · rintro ⟨hn_two, hrho_pos, hrho_lt_one⟩
    rw [bhattacharyya_iidPower_multiplicative]
    · exact pow_lt_self_of_lt_one₀ hrho_pos hrho_lt_one hn_two
    · exact fun i => mul_nonneg (hx.1 i) (hy.1 i)
  · constructor
    · intro hpower
      cases n with
      | zero => omega
      | succ k =>
          funext i
          have hi :
              law x i * (∑ z : IidSpace Outcome k, iidPower (law x) k z) =
                law y i * (∑ z : IidSpace Outcome k, iidPower (law y) k z) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            simpa [iidPower] using congrFun hpower (i, z)
          rw [iid_power_sum_one (law x) hx.2 k,
            iid_power_sum_one (law y) hy.2 k, mul_one, mul_one] at hi
          exact hi
    · intro hsame
      rw [hsame]

#print axioms finite_repetition_amplifies_without_crossing_law_kernel

end D5.S3.Estimation.ErrorExponents.FiniteRepetitionLawKernel
