# Finite-amplitude obstruction at matched occupation

## Abstract

A faithful two-mode CAR product family violates the proposed cubic entropy bound by 4Q*.

**Theorem 1.1 (Fixed-diagonal entropy slope).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.entropySlope_mul_le_fixedOccupationEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.entropySlope_mul_le_fixedOccupationEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For real a < b with a+b = 1 and 0 ≤ z < ab, put d = √((b−a)²+4z), λ± = (1±d)/2, and F(a,b,z) = ∑± λ± log λ± − a log a − b log b. Then F(a,b,z) ≥ z ψ(a,b), where ψ(a,b) = (log b − log a)/(b−a). Convexity of log(1+d) − log(1−d) makes its ratio to d nondecreasing, so the entropy derivative is bounded below by its value at z = 0.

**Theorem 1.2 (Scalar margin).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.finite_amplitude_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.finite_amplitude_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Assume 0 < a < b, a+b = 1, η > 0 and 0 < z ≤ abη/(2+η). With s = √(ab), r = √(ab−z), and α ψ(a,b) = 2(1+η)/(1+2s), the bound is 0 < ηz/(1+2s) ≤ α F(a,b,z) − 4s(s−r−z/(1+2r)). The amplitude bound controls the quadratic defect uniformly over this interval.

For a positive Gibbs half-gap h, put a = exp(−h)/(2 cosh h), b = exp(h)/(2 cosh h), c = cosh(h/3), η = (c−1)(c+2)/[2(2c+1)²], and zmax = abη/(2+η). Write α₃ = (9/2) sinh(h/3) sinh(2h/3)/(2h sinh h), the cubic coefficient in Wu v1, Remark 3.15, (3.55).

**Theorem 1.3 (Faithful CAR product states).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.matched_product_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.matched_product_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let w be complex with 0 < z = |w|² ≤ zmax. Put d = diag(a,b), let σ have diagonal (a,b) and off-diagonal entries w and its conjugate, and set ρ = d ⊗ σ and D = d ⊗ d. The matrices d, σ and ρ are positive definite with ordinary trace one. For each of the two signed CAR lowering jumps Jₖ, Aₖ = Re Tr(ρ JₖJₖ†) = a and Bₖ = Re Tr(ρ Jₖ†Jₖ) = b. With Tₖ = Re Tr(√ρ Jₖ √ρ Jₖ†), Q* = ∑ₖ √(AₖBₖ)(√(AₖBₖ) − Tₖ), and S = Re Tr(ρ(log ρ − log D)), the theorem gives 0 < ηz/(1+2√(ab)) ≤ α₃ S − 4Q*. The Gibbs factor makes the first quadratic defect zero. The second overlap is r + z/(1+2r), and S = F(a,b,z). The strict gap concerns the proposed bound α₃ S ≤ 4Q* for the entropy term in (3.54).

**Theorem 1.4 (An interval of distinct witnesses).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.amplitude_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.amplitude_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For each h > 0, zmax is positive. The map z ↦ ρ with w = √z is injective on 0 < z ≤ zmax. Every z in that interval is realized by a complex w with |w|² = z whose product state is positive definite of trace one and satisfies 4Q* < α₃ S.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.amplitude_interval`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.entropySlope_mul_le_fixedOccupationEntropy`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.finite_amplitude_obstruction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.matched_product_obstruction`
- Dependency: [D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison](TwistedTwoModeOUComparison.md)
