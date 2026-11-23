# The normalized Gibbs quartic at positive inverse temperature

## Abstract

Strict exponent decrease of the positive-temperature Wu quartic kernel.

Fix real inverse temperature β > 0. For q > 1 set x = β/(2q), y = β/2 − x, R = coth x and S = coth y. Write U = 1/sinh² x, V = 1/sinh² y and A = (y/x)(V/U). The reduced population and coherence coefficients are a = A/2, e = S − A(R − 1), and d = −1 + (1 − R/2)S + A(R − 1)²/2. The symmetric matrix K has diagonal a, d and both off-diagonal entries e/2. Write value(β,q,v) for vᵀ K v.

**Theorem 1.1 (Pointwise strict decrease).**

$$\operatorname{deriv}\left(\operatorname{valueAlongExponent}\left(beta, v\right), q\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.deriv_value_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real β > 0, q > 1 and every nonzero v in ℝ², the displayed derivative is negative. The function valueAlongExponent(β,v) sends t to value(β,t,v).

Set Λ = 2(R + S) − 1/x − 1/y. For s = v₀ − (R − 1)v₁ and t = v₁, the derivative is −x/(2q) times the quadratic form in (s,t) with leading entry AΛ, mixed matrix entry V + UA, and trailing entry US + RV. The determinant is V²/x² times the product of 2xy(R + S) − (x + y) and sinh x cosh x + sinh y cosh y, minus (x + y)² inside the same factor. Each product factor strictly exceeds x + y. The leading entry is positive and completion of the square proves strict positivity of the form for nonzero (s,t).

**Theorem 1.2 (Strict Loewner drop).**

$$0 < \operatorname{value}\left(beta, p, v\right) - \operatorname{value}\left(beta, r, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_drop_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real β > 0, 1 < p < r and every nonzero v in ℝ², the displayed difference is positive.

The mean value theorem applies to the quadratic form with the vector held fixed throughout the exponent interval.

**Theorem 1.3 (Strict Schur complement).**

$$0 < \operatorname{a}\left(beta, p\right) - \operatorname{a}\left(beta, r\right) \land 0 < \operatorname{d}\left(beta, p\right) - \operatorname{d}\left(beta, r\right) - \frac{\left(\operatorname{e}\left(beta, p\right) - \operatorname{e}\left(beta, r\right)\right)^{2}}{4 \cdot \left(\operatorname{a}\left(beta, p\right) - \operatorname{a}\left(beta, r\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_schur_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real β > 0 and 1 < p < r, write Δa = a(β,p) − a(β,r) and define Δe and Δd by the same endpoint difference. Both displayed inequalities hold.

Evaluate the positive endpoint form at (1,0) and at (−Δe/(2Δa),1).

**Theorem 1.4 (Agreement with the Gibbs exponent coefficients).**

$$\operatorname{K}\left(beta, q\right) = \operatorname{exponentK}\left(beta, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.K_eq_exponentK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real β > 0 and q > 1, the two reduced matrices agree. For z = exp(−β), k = z^(1/q), u = z/k, g = 1 − u and h = 1 − k, exponentK has the same arrangement of entries with a = (q − 1)(z/k²)h²/(2g²), e = 2/g − 1 − 2(q − 1)uh/g², and d = 2/g − 3/2 − (1 + z)/(gh) + 2(q − 1)z/g².

With x and y as above, k = exp(−2x), u = exp(−2y), z = ku and q − 1 = y/x. Substitute the exponential forms of the two hyperbolic cotangents and hyperbolic sines. The identity concerns the reduced coefficient matrices.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.K_eq_exponentK`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.deriv_value_neg`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_drop_pos`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_schur_pos`
- Dependency: [D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic](../../Entropy/RenyiCombining/ArimotoHyperbolic.md)
- Dependency: [D5/S3/Observer/Fluctuation/ThermalCoefficientFloor](../../Observer/Fluctuation/ThermalCoefficientFloor.md)
