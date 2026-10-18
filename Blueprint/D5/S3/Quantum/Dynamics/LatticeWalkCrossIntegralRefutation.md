# The lattice-walk cross-integral estimate fails

## Abstract

Early coherent amplitudes contradict the uniform lattice-walk cross-integral estimate.

All finite indices are natural numbers, i is the imaginary unit, and log is the natural logarithm. Integrals use Lebesgue measure on the real time axis, and the norm of a complex number is its modulus. In the exponentials, the indices are embedded in the real or complex numbers before subtraction, so j − k is the signed difference.

**Definition 1.1 (The oscillatory term of the cycle walk).**

$$\forall (n: \mathbb{N}), (\forall (l: \mathbb{Z}), (\forall (t: \mathbb{R}), (\operatorname{walkTerm}\left(n, l, t\right) = \sum_{(j: \mathbb{N}), 0 \le j, j < n} (\sum_{(k: \mathbb{N}), 0 \le k, k < n, (j \ne k) \land (j + k \ne n)} (\exp\left(-(i \cdot t \cdot \sin\left(\frac{\pi \cdot (j + k)}{n}\right) \cdot \sin\left(\frac{\pi \cdot (j - k)}{n}\right))\right) \cdot \exp\left(\frac{2 \cdot \pi \cdot i \cdot l \cdot (j - k)}{n}\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.walkTerm` (`✓ std3`).

*Citation.* Shyam Dhamapurkar; Xiu-Hao Deng (2023). *Quantum walk mixing is faster than classical on periodic lattices*. DOI: [10.1016/j.physa.2023.129252](https://doi.org/10.1016/j.physa.2023.129252). URL: <https://arxiv.org/abs/2309.16352v1>.

*Commentary.*

For every natural n, integer displacement l and real time t, walkTerm(n,l,t) is the complex double sum in Eq. (B8). It omits the diagonal j = k and the antidiagonal j + k = n. The last exponential equals w raised to l(j − k), where w = exp(2πi/n), so l is the displacement q − p. When n = 0 both index ranges are empty and the sum is zero.

**Definition 1.2 (The proposed uniform cross-integral bound).**

$$\operatorname{claim} \Leftrightarrow (\forall (n_{1}: \mathbb{N}), (\forall (n_{2}: \mathbb{N}), ((\operatorname{Odd}\left(n_{1}\right)) \Rightarrow ((\operatorname{Odd}\left(n_{2}\right)) \Rightarrow ((\gcd\left(n_{1}, n_{2}\right) = 1) \Rightarrow ((n_{2} < n_{1}) \Rightarrow (\forall (l_{1}: \mathbb{N}), (\forall (l_{2}: \mathbb{N}), ((l_{1} < n_{1}) \Rightarrow ((l_{2} < n_{2}) \Rightarrow (\forall (T: \mathbb{R}), ((0 \le T) \Rightarrow (\left\lVert \int_{0}^{T} (\operatorname{walkTerm}\left(n_{1}, l_{1}, t\right) \cdot \operatorname{walkTerm}\left(n_{2}, l_{2}, t\right)) dt \right\rVert \le 32 \cdot n_{1} \cdot (n_{2} \cdot \log\left(n_{2}\right))^{2} + 32 \cdot n_{2} \cdot (n_{1} \cdot \log\left(n_{1}\right))^{2})))))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.claim` (`✓ std3`).

*Citation.* Shyam Dhamapurkar; Xiu-Hao Deng (2023). *Quantum walk mixing is faster than classical on periodic lattices*. DOI: [10.1016/j.physa.2023.129252](https://doi.org/10.1016/j.physa.2023.129252). URL: <https://arxiv.org/abs/2309.16352v1>.

*Commentary.*

Equation (15), the two-dimensional estimate used after Conjecture 1, asserts this bound for every pair of odd, coprime natural orders n₁ > n₂, every pair of natural displacements l₁ < n₁ and l₂ < n₂, and every real T ≥ 0. The two factors are evaluated at the same time t. The right side is 32n₁(n₂ log n₂)² + 32n₂(n₁ log n₁)² and is independent of T.

**Theorem 1.3 (A counterexample at unit time).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/dhamapurkar-deng-2023-lattice-walk-cross-integral-refutation` (refuted) by `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dhamapurkar-deng-2023-lattice-walk-cross-integral-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shyam Dhamapurkar; Xiu-Hao Deng (2023). *Quantum walk mixing is faster than classical on periodic lattices*. DOI: [10.1016/j.physa.2023.129252](https://doi.org/10.1016/j.physa.2023.129252). URL: <https://arxiv.org/abs/2309.16352v1>.

*Commentary.*

Take n₂ = 10¹⁰ + 1, n₁ = 10¹⁰ + 3, l₁ = l₂ = 1 and T = 1. The two orders are odd and coprime: any common divisor divides their difference 2, and an odd number has no even divisor. Both displacements lie in the required ranges.

For an odd natural n ≥ 3 and real t, write A_n(t) = Σ_{0≤j<n} exp(i(t/2)cos(2πj/n)) exp(2πij/n). The cosine difference identity expands |A_n(t)|² into the full double sum. Its diagonal contributes n. Its antidiagonal, disjoint from the diagonal for odd n, contributes −1 by the sum of the nontrivial powers of exp(4πi/n). Consequently walkTerm(n,1,t) = |A_n(t)|² − (n − 1), a real number.

For every natural n ≥ 3, pairing j with n − j cancels the sine-cosine cross terms in the imaginary part of A_n(t). The identity Σ_{0≤j<n} cos²(2πj/n) = n/2 and the inequality u sin u ≥ u²/2 for |u| ≤ 1/2 give Im A_n(t) ≥ nt/8 for 0 < t ≤ 1. Hence |A_n(t)|² ≥ n²/256 on [1/2,1]. The triangle inequality also gives 0 ≤ |A_n(t)|² ≤ n² for every real t.

For odd n₁,n₂ ≥ 3, expand the product using these two real identities. Bound each subtracted squared modulus by nᵢ² and discard the nonnegative constant (n₁ − 1)(n₂ − 1). The product of the squared moduli is nonnegative on [0,1] and at least n₁²n₂²/65536 on [1/2,1]. Thus its real integral satisfies ∫₀¹ walkTerm(n₁,1,t)walkTerm(n₂,1,t) dt ≥ n₁²n₂²/131072 − (n₁ − 1)n₂² − (n₂ − 1)n₁².

At the stated orders, 0 ≤ log n₂ ≤ log n₁ ≤ 34 log 2 < 24, since n₁ < 2³⁴. The proposed upper bound is therefore at most 32·24²(n₁n₂² + n₂n₁²), which is strictly smaller than the integral lower bound above. The norm of the integral is at least its real value, contradicting Eq. (15).

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.walkTerm`
- Dependency: [D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros](EndAmplitudeCosineSumZeros.md)
