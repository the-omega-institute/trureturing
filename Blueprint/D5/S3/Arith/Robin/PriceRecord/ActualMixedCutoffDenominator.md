# Conditional actual mixed cutoff denominator separation

## Abstract

ActualMixedCutoffDenominator

The actual clamped cutoff offsets d(j,X)=j log(cutoff j(referencePrice X))-log X supply U and V from ActualMixedCutoffFourthOrder. With L=log X, L^3 U tends to 2(log 2)^2, L^3 V tends to 2 log 2(log 3-log 2), and L^4((log 3-log 2)U-log 2 V) tends to 3(log 2)^2 log 3(log 3-log 2). The third coefficient separates the leading proportional terms. The expansion proof consumes P and actual_quartic_error at the six fixed indices 2,3,4,6,8,12, retains the fourth-order error, and divides by d(2,X) only through its positive limit log 2.

For integer labels u and v with 1<=u, 1<=v and the positive logarithmic gap 0<(log 3-log 2)u-log 2*v, integer_power_log_gap gives exp(-log 3*u) <= (log 3-log 2)u-log 2*v. After normalizing x=h/L^3, the fourth-order separation makes the label gap positive. Taking logarithms gives an inequality for log L; under h<=C L^3 log L its limiting coefficient is C*2(log 2)^2 log 3<1, a contradiction. This live argument is the content of the private eventual_two_resonance_denominator helper consumed by the final theorem. The expansion assembly and the discrete-gap helper are consumed proof components, not separate terminal admission claims.

The external suppliers are beta>=37/50, beta<3/4, C0>=0, positive rho8 and rho12, a clock barL with barL-log X tending to zero, and the exact mode-8 and mode-12 exponential paid lower bounds in the statement below. paid_range_rate converts each paid bound to a log^4/range error rate. For each fixed 0<C<1/(2(log 2)^2 log 3), one eventual threshold in X precedes every integer h,u,v with h>=1 satisfying the two resonance errors. There is no upper bound on h and no theta, A3 or determinant premise. The retained beta<3/4 assumption is not used by this proof.

This conditional result excludes small simultaneous resonance denominators. It produces no paid mode-8/mode-12 ranges, clock, fee certificate, original-record labels or fixed-B original-e substitution. Larger denominators, full original-record coverage, remaining paid-prefix repair and the full Robin/5040/RH conclusion remain open. The derivation uses repository results and pinned Mathlib analysis; no literature-novelty or external open-problem resolution is asserted.

**Theorem 1.1 (actual_mixed_denominator_expansions).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator.actual_mixed_denominator_expansions`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator.actual_mixed_denominator_expansions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem actual_mixed_denominator_expansions : Tendsto (fun X : ℝ => log X ^ 3 * U X) atTop (𝓝 (2 * log 2 ^ 2)) ∧ Tendsto (fun X : ℝ => log X ^ 3 * V X) atTop (𝓝 (2 * log 2 * (log 3 - log 2))) ∧ Tendsto (fun X : ℝ => log X ^ 4 * ((log 3 - log 2) * U X - log 2 * V X)) atTop (𝓝 (3 * log 2 ^ 2 * log 3 * (log 3 - log 2)))

**Theorem 1.2 (eventual_actual_mixed_denominator).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator.eventual_actual_mixed_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator.eventual_actual_mixed_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem eventual_actual_mixed_denominator (beta C0 rho8 rho12 : ℝ) (barL : ℝ → ℝ) (M N : ℝ → ℕ) (hbeta : 37 / 50 ≤ beta) (hbeta' : beta < 3 / 4) (hC0 : 0 ≤ C0) (hrho8 : 0 < rho8) (hrho12 : 0 < rho12) (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0)) (hpaid8 : ∀ᶠ X : ℝ in atTop, rho8 * exp (((1 - beta) / 8 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ (M X : ℝ) + 1) (hpaid12 : ∀ᶠ X : ℝ in atTop, rho12 * exp (((1 - beta) / 12 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ (N X : ℝ) + 1) : ∀ C : ℝ, 0 < C → C < 1 / (2 * log 2 ^ 2 * log 3) → ∀ᶠ X : ℝ in atTop, ∀ h u v : ℤ, 1 ≤ h → |(h : ℝ) * U X - u| ≤ C0 / ((M X : ℝ) + 1) → |(h : ℝ) * V X - v| ≤ C0 / ((N X : ℝ) + 1) → C * log X ^ 3 * log (log X) < (h : ℝ)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator.actual_mixed_denominator_expansions`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffDenominator.eventual_actual_mixed_denominator`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder](ActualMixedCutoffFourthOrder.md)
