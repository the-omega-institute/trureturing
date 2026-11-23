# The normalized Gibbs quartic at positive inverse temperature

## Abstract

Strict exponent decrease of the positive-temperature Wu quartic kernel.

Wu v1, §3.2, Corollary 3.2 and (3.19), supplies the one-qubit Gibbs dynamics. In the scalar reduction, divide the weighted fourth-order coefficients by the square of the second-order coherence coefficient and translate the population coordinate by writing its original value as s + 1. The resulting coefficients and their strict comparison are derived here. Lean checks the reduced scalar formulas at β > 0 and real exponents above one. The signed-model Taylor identification and Wu’s Conjecture 3.14 lie outside these statements.

Fix real inverse temperature β > 0. For q > 1 set x = β/(2q), y = β/2 − x, R = coth x and S = coth y. Write U = 1/sinh² x, V = 1/sinh² y and A = (y/x)(V/U). The reduced population and coherence coefficients are a = A/2, e = S − A(R − 1), and d = −1 + (1 − R/2)S + A(R − 1)²/2. The symmetric matrix K has diagonal a, d and both off-diagonal entries e/2. Write value(β,q,v) for vᵀ K v. The function valueAlongExponent(β,v) sends t to value(β,t,v).

In the exponential coordinates set z = exp(−β), k = z^(1/q), u = z/k, g = 1 − u and h = 1 − k. Then exponentA = (q − 1)(z/k²)h²/(2g²), exponentE = 2/g − 1 − 2(q − 1)uh/g², and exponentD = 2/g − 3/2 − (1 + z)/(gh) + 2(q − 1)z/g². Write ΔA = exponentA(β,p) − exponentA(β,r), with ΔE and ΔD defined by the respective endpoint differences.

**Theorem 1.1 (Pointwise strict decrease).**

$$\forall beta \in \mathbb{R}, q \in \mathbb{R}, v \in \mathbb{R}^{2},\; \left(0 < beta \land \left(1 < q \land v \ne 0\right)\right) \Rightarrow \operatorname{deriv}\left(\operatorname{valueAlongExponent}\left(beta, v\right), q\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.deriv_value_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Set Λ = 2(R + S) − 1/x − 1/y. For s = v₀ − (R − 1)v₁ and t = v₁, the derivative is −x/(2q) times the quadratic form in (s,t) with leading entry AΛ, mixed matrix entry V + UA, and trailing entry US + RV. The determinant is V²/x² times the product of 2xy(R + S) − (x + y) and sinh x cosh x + sinh y cosh y, minus (x + y)² inside the same factor. The reciprocal bound for coth gives Λ ≥ 1/x + 1/y > 0 and bounds the first product factor below by x + y. The second product factor strictly exceeds x + y, so the determinant is positive. Completion of the square gives strict positivity of the form for nonzero (s,t).

**Theorem 1.2 (Strict Loewner drop).**

$$\forall beta \in \mathbb{R}, p \in \mathbb{R}, r \in \mathbb{R}, v \in \mathbb{R}^{2},\; \left(\left(0 < beta \land \left(1 < p \land p < r\right)\right) \land v \ne 0\right) \Rightarrow 0 < \operatorname{value}\left(beta, p, v\right) - \operatorname{value}\left(beta, r, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_drop_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The mean value theorem applies to the quadratic form with the vector held fixed throughout the exponent interval.

**Theorem 1.3 (Strict Schur complement).**

$$\forall beta \in \mathbb{R}, p \in \mathbb{R}, r \in \mathbb{R},\; \left(0 < beta \land \left(1 < p \land p < r\right)\right) \Rightarrow \left(0 < \operatorname{a}\left(beta, p\right) - \operatorname{a}\left(beta, r\right) \land 0 < \operatorname{d}\left(beta, p\right) - \operatorname{d}\left(beta, r\right) - \frac{\left(\operatorname{e}\left(beta, p\right) - \operatorname{e}\left(beta, r\right)\right)^{2}}{4 \cdot \left(\operatorname{a}\left(beta, p\right) - \operatorname{a}\left(beta, r\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_schur_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Write Δa, Δe and Δd for the hyperbolic endpoint differences. Evaluate the positive endpoint form at (1,0) and at (−Δe/(2Δa),1).

**Theorem 1.4 (Positive attained minimum for the Gibbs coefficients).**

$$\forall beta \in \mathbb{R}, p \in \mathbb{R}, r \in \mathbb{R},\; \left(0 < beta \land \left(1 < p \land p < r\right)\right) \Rightarrow \left(0 < \Delta A \land \left(0 < \Delta D - \frac{\Delta E^{2}}{4 \cdot \Delta A} \land \Delta D - \frac{\Delta E^{2}}{4 \cdot \Delta A} = \min_{s \in \mathbb{R}} (\Delta A \cdot s^{2} + \Delta E \cdot s + \Delta D)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCriticalQuartic.exponent_endpoint_schur_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Use k = exp(−2x), u = exp(−2y), z = ku and q − 1 = y/x to identify the coefficients at both endpoints. Completing the square in the exponential endpoint polynomial gives the lower bound and shows that it is attained at s = −ΔE/(2ΔA).

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.deriv_value_neg`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_drop_pos`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.endpoint_schur_pos`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCriticalQuartic.exponent_endpoint_schur_pos`
- Dependency: [D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic](../../Entropy/RenyiCombining/ArimotoHyperbolic.md)
- Dependency: [D5/S3/Observer/Fluctuation/ThermalCoefficientFloor](../../Observer/Fluctuation/ThermalCoefficientFloor.md)
