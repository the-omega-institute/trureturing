# Cubic occupation envelope

## Abstract

An occupation bound for the directed cubic spectral sum.

**Theorem 1.1 (Strict lower bound under the CAR constraints).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicOccupationEnvelope.cubic_deficit_gt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicOccupationEnvelope.cubic_deficit_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Fix the ascending spectrum λ = (262144, 531441, 551368, 1030301)/2375254 and h = 3 log(9/8). Let w be nonnegative directed weights with ∑ⱼ(wᵢⱼ + wⱼᵢ) = 2 and wᵢⱼ + wⱼᵢ ≤ 1 for i < j. Let eᵢ ∈ [0,1] satisfy ∑ᵢ eᵢ = 2 and wᵢᵢ = eᵢ(1 − eᵢ). The directed moment ∑ᵢ<ⱼ(wᵢⱼ − wⱼᵢ)(λⱼ − λᵢ) is 2m, where |m| ≤ ∑ᵢ eᵢ|λᵢ − v| for every real v.

Write xᵢ = λᵢ^(1/3). The directed energy is E₃(w) = (9/(8 cosh h)) ∑ᵢⱼ wᵢⱼ [exp(h)λᵢ + exp(−h)λⱼ − exp(h/3)xᵢ²xⱼ − exp(−h/3)xᵢxⱼ²]. With α₃ = (9/2) sinh(h/3) sinh(2h/3)/(2h sinh h) and H(m) = ∑ᵢ λᵢ log(4λᵢ) + 2 log(cosh h) − 2hm, the normalized deficit (4 cosh(h)/9)(E₃(w) − α₃ H(m)) exceeds 1/8000.

The cubic expansion yields a symmetric edge cost, a linear term in m, and a nonnegative reverse-edge contribution. The symmetric cost separates into a reference cost, nonnegative edge corrections and a weighted sum of (eᵢ − 1/2)². Centering the spectral distances in the moment bound and applying weighted Cauchy–Schwarz bounds this sum from below. Completing the square and enclosing the logarithms by rational bounds gives the stated margin.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicOccupationEnvelope.cubic_deficit_gt`
