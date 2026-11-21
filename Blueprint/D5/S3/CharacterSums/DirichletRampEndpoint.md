# The endpoint comparison

## Abstract

The logarithmic derivative at one from a finite Mangoldt ramp

Let χ be a nonprincipal complex Dirichlet character of positive modulus N. Write D for L′(1,χ)/L(1,χ). For real x the host readout g(x) is xD plus the sum of Λ(n)χ(n) max(x/n − 1, 0) over positive integers n ≤ x. Let γ be Euler’s constant and let T(x) be the integral of (ψ(u) − u)/u² over u > x, where ψ is the inclusive Chebyshev sum over prime powers.

**Theorem 1.1 (A signed tail bound for every real endpoint x ≥ 2).**

$$\operatorname{abs}\left(D\right) \le \operatorname{abs}\left(\operatorname{g}\left(x\right)\right)/x+\operatorname{log}\left(x\right)-1-gamma-\operatorname{T}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampEndpoint.logDerivative_le_ramp_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each included integer n, the positive part equals x/n − 1, including its zero value when n = x. The character has norm at most one. After division by x the norm of its ramp is at most the sum of Λ(n)/n minus ψ(x)/x. The complete Chebyshev tail identity evaluates this difference as log x − 1 − γ − T(x). Subtract the ramp from g(x) and apply the triangle inequality.

**Theorem 1.2 (An additive bound uniform in the modulus and character).**

$$\operatorname{abs}\left(\operatorname{g}\left(x\right)\right) \le x^{1/2+epsilon} \Rightarrow \operatorname{abs}\left(D\right) \le \operatorname{log}\left(x\right)-1-gamma+eta$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampEndpoint.uniform_logDerivative_of_ramp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real ε < 1/2 and η > 0 there is a real X ≥ 2 such that the implication holds for every real x ≥ X and every nonprincipal χ of every positive modulus. Division of the assumed bound by x gives x raised to ε − 1/2. This power tends to zero, as does the signed integral T(x). Choose one threshold beyond which each contributes at most η/2.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletRampEndpoint.logDerivative_le_ramp_tail`
- Truth anchor: `D5/S3/CharacterSums/DirichletRampEndpoint.uniform_logDerivative_of_ramp`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace](../Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](../Weil/Mertens/WeightedPrimeLimit.md)
