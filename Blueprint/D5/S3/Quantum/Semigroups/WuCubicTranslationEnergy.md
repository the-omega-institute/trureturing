# Scalar translations of the Wu cubic energy

## Abstract

Exact charge-weighted slope and centered degree gap for the Wu cubic translation energy.

Take r ≥ 1 unless otherwise specified. Write B = G² and U(X) = GXG, with G⁶ = D the two-mode Gibbs density. The cubic energy is (9/8) Re Tr(U(X)² U(LX)), where L is the signed generator. The variance V(A) is Re Tr(B U(A)²).

## Stationarity and the trace slope

**Theorem 1.1 (Gibbs stationarity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.stationary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.stationary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every complex direction A, Tr(D L(A)) = 0. Pairing with the identity extracts the degree-zero coordinate, which the generator annihilates.

**Theorem 1.2 (Affine energy along scalar translations).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_translate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For any complex A and real t, L(A + tI) = L(A) and U(A + tI) = U(A) + tB. The quadratic coefficient vanishes by cyclicity of trace and stationarity. The energy at A + tI is the energy at A plus t times (9/8) Re Tr((B U(A) + U(A) B) U(L(A))).

**Theorem 1.3 (Derivative in trace form).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every complex A, the trace coefficient of the affine formula is the derivative at every real t.

## Variance on signed charge blocks

**Theorem 1.4 (Entry multiplier on the support of a direction).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.entryMultiplier_of_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.entryMultiplier_of_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Write bᵢ for the ith diagonal entry of B. At each nonzero entry (i,j) of a basis direction of signed charge q, the modular eigenrelation gives bᵢ/bⱼ = r^q. The ratio of the ordinary variance weight to the Gibbs pairing weight is therefore m(q) = (r^q + 1)/(2√(r^q)).

**Theorem 1.5 (Diagonal ordinary-trace variance pairing).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.vPairing_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.vPairing_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For arbitrary complex X and Y, the pairing is half the trace of (B U(X)ᴴ + U(X)ᴴ B) U(Y). The charge multiplier rescales each Gibbs-orthogonal direction, so the pairing is the sum of the conjugate X-coordinate times the Y-coordinate times m(q) and the squared Gibbs norm of that direction.

**Theorem 1.6 (Entry formula for Hermitian directions).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.V_eq_entries`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.V_eq_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every real r and Hermitian A, V(A) is the sum of |Aᵢⱼ|² weighted by bᵢ bⱼ (bᵢ + bⱼ)/2. Hermiticity identifies the real part of the pairing of A with itself with the original trace variance.

**Theorem 1.7 (Variance weight of a single complex component).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.vWeight_eq_component`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.vWeight_eq_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For any complex A and basis label k, let Z be the kth coordinate of A times its basis direction. The variance weight wₖ is the squared modulus of that coordinate times the charge-rescaled squared Gibbs norm. It equals the same entry-weighted sum of |Zᵢⱼ|², including when Z is non-Hermitian.

**Theorem 1.8 (Variance as a sum of component weights).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.V_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.V_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian A, V(A) is the sum of the sixteen nonnegative weights wₖ.

## Degree-weighted slope and centered gap

**Theorem 1.9 (Exact charge-weighted derivative).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian A and every real t, the derivative of the cubic energy at A + tI along the translation is (9/4) times the sum of dₖ wₖ. Here dₖ is the generator degree of the kth signed thermal direction.

**Theorem 1.10 (Degree gap for the centered variance).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.degree_sum_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.degree_sum_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If A is Hermitian and Tr(DA) = 0, the identity coordinate vanishes. The degree-one mass V₁ contributes once and all other surviving weights contribute at least twice. The sum of dₖ wₖ is at least 2V − V₁.

**Theorem 1.11 (Lower bound for the translation derivative).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_deriv_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_deriv_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every Gibbs-centered Hermitian A and real t, the derivative at t is at least (9/4)(2V − V₁).

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.V_eq_entries`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.V_eq_sum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_deriv_ge`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_degree`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_trace`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.cubicEnergy_translate`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.degree_sum_ge`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.entryMultiplier_of_direction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.stationary`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.vPairing_expansion`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.vWeight_eq_component`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality](WuCubicThermalOrthogonality.md)
