# Exact affinity stability at exponent two

## Abstract

Sharp scalar affinity stability for Wu's normalized one-mode two-deficit on the closed qubit spectrum.

Use the normalized deficit of WuQubitSharpTwoRigidity with h = β/2, spectral polarization v, and Gibbs-axis direction z. Put k(h) = thermalBias(h) = tanh(h/2), t = v/(1+spectralRoot(v)), and J(u) = affinityJ(u). The scalar affinity defect is 1−(1+t k(h) z)/√((1+t²)(1+k(h)²)). The bound includes the repeated spectrum and rank-one endpoint.

**Theorem 1.1 (Integral kernel for the exact affinity coefficient).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.affinityJ_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.affinityJ_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every real u, affinityJ(u) is the interval integral of (1−x²)/(1−u x²)² on x ∈ [0,1]. On the coefficient range u ∈ [0,1), this is the positive radial integral entering the sharp constant.

**Theorem 1.2 (Exact scalar affinity coefficient).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every real h, with k(h) = thermalBias(h) = tanh(h/2), exactAffinityCoefficient(h) = (cosh(h) k(h)²/(1+k(h)²) + 1/(4 sharpCoefficient(h) affinityJ(k(h)²)))⁻¹. It is the coefficient for the squared loss of the ordinary-trace square-root affinity to the Gibbs point.

**Theorem 1.3 (Positivity at nonnegative temperature).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For h ≥ 0, exactAffinityCoefficient(h) is strictly positive.

**Theorem 1.4 (Tracial value of the exact coefficient).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At h = 0, exactAffinityCoefficient(0) = 4/3.

**Theorem 1.5 (Exact closed-spectrum affinity bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.normalizedDeficit_exactAffinity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.normalizedDeficit_exactAffinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For h ≥ 0, v ∈ [0,1], and z ∈ [−1,1], let t = v/(1+spectralRoot(v)). Then exactAffinityCoefficient(h) times normalizedAffinityDefect(h,t,z)² is at most normalizedDeficit(h,v,z), with strictness unless v = tanh(h) and (h = 0 or z = 1). The bound includes the repeated spectrum and rank-one endpoint.

**Theorem 1.6 (Sharpness along faithful spectra).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.normalizedDeficit_exactAffinity_sharp_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.normalizedDeficit_exactAffinity_sharp_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For h ≥ 0, the normalized deficit divided by the squared affinity defect tends to exactAffinityCoefficient(h) as t decreases to thermalBias(h) from above with z = exactAffinitySharpAlignment(h,t). The path has 0 < polarizationOfHalf(t) < 1, so its spectral states are faithful.

**Theorem 1.7 (Greatest scalar affinity coefficient).**

Lean statement: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_isGreatest`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For h ≥ 0, exactAffinityCoefficient(h) is the greatest c for which c times normalizedAffinityDefect(h,t,z)² ≤ normalizedDeficit(h,polarizationOfHalf(t),z) for every t ∈ [0,1] and z ∈ [−1,1]. This is the exact scalar one-mode optimality statement.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.affinityJ_eq_integral`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_eq`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_isGreatest`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_pos`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.exactAffinityCoefficient_zero`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.normalizedDeficit_exactAffinity`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.normalizedDeficit_exactAffinity_sharp_limit`
- Dependency: [D5/S3/Quantum/Semigroups/WuQubitSharpTwoRigidity](WuQubitSharpTwoRigidity.md)
