# Actual mixed cutoff fourth-order curvature

## Abstract

ActualMixedCutoffFourthOrder

The six roots are the actual clamped cutoffs at referencePrice X. Their normalized mixed area has positive fourth-order coefficient 3 log 2 log 3 log(3/2). The proof uses the existing normalized gain error, its arbitrary log-power limit, the existing nonnegative secant bound, and the pinned Mathlib fourth-order logarithm remainder. No quartic remainder is discarded before scaling. The integer consequence derives the log-power rates from external paid-growth suppliers and normalizes by h squared, giving one threshold before all h,p,u,v with h at least one. No upper bound on h is used. Positive determinants survive. Actual original clocks, fee certificates, ranges, fixed-B original-e substitution, full record coverage and the full RH/Robin goal remain external and open. Reg audit is unfinished: exact source bridges do not establish four-slot registration.

Set L=log X and alpha_j=d(j,X)=j log(cutoff j(referencePrice X))-L for j=2,3,4,6,8,12. Then theta=alpha_3/alpha_2, NU=3 alpha_4-alpha_8-3 alpha_2, NV=alpha_2-2 alpha_4+alpha_8-alpha_3+2 alpha_6-alpha_12, U=NU/alpha_2, V=NV/alpha_2 and A=(theta-1)U-V. Cross multiplication gives numerator (alpha_3-alpha_2)NU-alpha_2 NV and denominator alpha_2^2. Its quartic numerator coefficient is 3(log 2)^3 log 3(log 3-log 2). The actual-root limit alpha_2 -> log 2 > 0 permits division, yielding kappa=3 log 2 log 3 log(3/2). The polynomial residual and logarithm remainder are controlled before secant transfer to each actual root. The integer proof divides the exact determinant identity by h^2 before bounding errors; exponential domination and barL/log X -> 1 derive the required log^4/range rates from the three external paid-growth lower bounds.

The public polynomial P and actual_quartic_error retain the actual-root quartic remainder and are consumed by ActualMixedCutoffDenominator.actual_mixed_denominator_expansions. The public paid_range_rate retains its full real-function and positive-parameter telescope and is consumed for both mode-8 and mode-12 errors by eventual_actual_mixed_denominator, as well as by the integer determinant theorem here. P is a definition. These visibility exposures preserve their original bodies and supply no clock, paid range or fee producer.

**Definition 1.1 (P).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.P`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact definition: def P (s : ℝ) : Polynomial ℝ := Polynomial.C s - Polynomial.C s * Polynomial.X + Polynomial.C (s + s ^ 2 / 2) * Polynomial.X ^ 2 - Polynomial.C (s + 3 * s ^ 2 / 2 + s ^ 3 / 3) * Polynomial.X ^ 3 + Polynomial.C (s + 3 * s ^ 2 + 11 * s ^ 3 / 6 + s ^ 4 / 4) * Polynomial.X ^ 4

**Theorem 1.2 (actual_quartic_error).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_quartic_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_quartic_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem actual_quartic_error {j : ℕ} (hj : 2 ≤ j) : Tendsto (fun X : ℝ => log X ^ 4 * (d j X - (P (log j)).eval (1 / log X))) atTop (𝓝 0)

**Theorem 1.3 (paid_range_rate).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.paid_range_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.paid_range_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem paid_range_rate {barL range : ℝ → ℝ} {rho lambda : ℝ} (hrho : 0 < rho) (hlambda : 0 < lambda) (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0)) (hpaid : ∀ᶠ X : ℝ in atTop, rho * exp (lambda * barL X) * barL X ^ 2 ≤ range X) : (∀ᶠ X : ℝ in atTop, 0 < range X) ∧ Tendsto (fun X => log X ^ 4 / range X) atTop (𝓝 0)

**Theorem 1.4 (actual_mixed_curvature_tendsto).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_mixed_curvature_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_mixed_curvature_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem actual_mixed_curvature_tendsto: Tendsto (fun X : ℝ => log X ^ 4 * A X) atTop (𝓝 kappa)

**Theorem 1.5 (kappa_pos).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.kappa_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.kappa_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem kappa_pos: 0 < kappa

**Theorem 1.6 (actual_mixed_curvature_lower).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_mixed_curvature_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_mixed_curvature_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem actual_mixed_curvature_lower: ∀ᶠ X : ℝ in atTop, 0 < log X ∧ kappa / (2 * log X ^ 4) ≤ A X

**Theorem 1.7 (eventual_integer_determinant_positive).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.eventual_integer_determinant_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.eventual_integer_determinant_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem eventual_integer_determinant_positive(beta C0 rho3 rho8 rho12 : ℝ) (barL A3 : ℝ → ℝ) (M N : ℝ → ℕ) (hbeta : 37 / 50 ≤ beta) (hbeta' : beta < 3 / 4) (hC0 : 0 ≤ C0) (hrho3 : 0 < rho3) (hrho8 : 0 < rho8) (hrho12 : 0 < rho12) (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0)) (hpaid3 : ∀ᶠ X : ℝ in atTop, rho3 * exp (((1 - beta) / 3 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ A3 X) (hpaid8 : ∀ᶠ X : ℝ in atTop, rho8 * exp (((1 - beta) / 8 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ (M X : ℝ) + 1) (hpaid12 : ∀ᶠ X : ℝ in atTop, rho12 * exp (((1 - beta) / 12 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ (N X : ℝ) + 1) : ∀ᶠ X : ℝ in atTop, ∀ h p u v : ℤ, 1 ≤ h → |(h : ℝ) * theta X - p| ≤ C0 / A3 X → |(h : ℝ) * U X - u| ≤ C0 / ((M X : ℝ) + 1) → |(h : ℝ) * V X - v| ≤ C0 / ((N X : ℝ) + 1) → 1 ≤ (p - h) * u - h * v

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.P`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_mixed_curvature_lower`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_mixed_curvature_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.actual_quartic_error`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.eventual_integer_determinant_positive`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.kappa_pos`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder.paid_range_rate`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature](ActualTwoFourCutoffCurvature.md)
