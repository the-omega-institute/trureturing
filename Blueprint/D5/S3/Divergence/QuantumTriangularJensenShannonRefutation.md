# QTD squared can exceed QJS2

## Abstract

A full-rank commuting qubit pair has quantum triangular discrimination squared greater than base-2 quantum Jensen–Shannon divergence.

Yupan Liu, Quantum state testing beyond the polarizing regime and quantum triangular discrimination, arXiv:2303.01952v5; Computational Complexity 34 (2025), article 11. §1.3, Improved inequalities on the quantum triangular discrimination, printed p. 7, verbatim: “We observe that Theorem 1.4(ii) is not tight. Numerical simulations indicate that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) for any states ρ₀ and ρ₁.” After Theorem 3.4, verbatim: “Numerical simulations suggest that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁), while we only managed to prove a slightly weaker bound ½QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) in Theorem 3.4.”

**Definition 1.1 (Quantum Jensen–Shannon divergence).**

$$\forall n: \mathbb{N}, \forall rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{QJS2}\left(rho, sigma\right) = \operatorname{vonNeumann2}\left((\frac{1}{2}) \cdot (rho + sigma)\right) - \frac{\operatorname{vonNeumann2}\left(rho\right) + \operatorname{vonNeumann2}\left(sigma\right)}{2}$$

*Formalization.* `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.QJS2` (`✓ std3`).

*Citation.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

Definition 2.10 with base-2 logarithms is the entropy of the average state minus the average entropy.

**Definition 1.2 (Quantum triangular discrimination).**

$$\forall n: \mathbb{N}, \forall rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{QTD}\left(rho, sigma\right) = \frac{\operatorname{re}\left(\operatorname{trace}\left(\left(rho - sigma\right) \cdot \operatorname{cfc}\left((x \mapsto x^{\frac{- 1}{2}}), rho + sigma\right) \cdot \left(rho - sigma\right) \cdot \operatorname{cfc}\left((x \mapsto x^{\frac{- 1}{2}}), rho + sigma\right)\right)\right)}{2}$$

*Formalization.* `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.QTD` (`✓ std3`).

*Citation.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

Definition 3.1 uses the inverse square root of the sum between two copies of the difference. The function x↦x^(−1/2) has value zero at zero in the real-power convention, so the inverse acts on the support of the sum.

**Definition 1.3 (The proposed lower inequality).**

$$claim \Leftrightarrow \forall n: \mathbb{N}, \forall rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{IsState}\left(rho\right)) \Rightarrow ((\operatorname{IsState}\left(sigma\right)) \Rightarrow (\operatorname{QTD}\left(rho, sigma\right)^{2} \le \operatorname{QJS2}\left(rho, sigma\right)))$$

*Formalization.* `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.claim` (`✓ std3`).

*Citation.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

For every finite dimension and every pair of quantum states, the assertion requires QTD²≤QJS₂. This is the lower conjunct of the proposed two-sided bound.

**Theorem 1.4 (A commuting qubit counterexample).**

$$\neg (\forall n: \mathbb{N}, \forall rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{IsState}\left(rho\right)) \Rightarrow ((\operatorname{IsState}\left(sigma\right)) \Rightarrow (\operatorname{QTD}\left(rho, sigma\right)^{2} \le \operatorname{QJS2}\left(rho, sigma\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-2025-qtd-qjs-lower-bound-refutation` (refuted) by `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-2025-qtd-qjs-lower-bound-refutation","declaration_gid":"D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

Take ρ=diag(255/256,1/256) and σ=diag(1/256,255/256). Both states have strictly positive diagonal entries and unit trace. Their sum is the identity, so its inverse square root is the identity. The difference has diagonal entries 127/128 and −127/128, giving QTD=(127/128)². The average is the maximally mixed qubit state with entropy one. Both input entropies equal h(1/256), where h(a)=−a log₂ a−(1−a) log₂(1−a). Since log₂(1/256)=−8 and log₂(255/256)<0, h(1/256)≥1/32. Thus QJS₂≤31/32<(127/128)⁴=QTD², and QTD²−QJS₂≥97793/268435456. The matrices commute, so the failure already occurs for classical probability distributions. The general family diag(1−a,a), diag(a,1−a) has Q=(1−2a)² and J=1−h(a). Mathematical reasoning, not additional formal theorems here, gives (1−J)/(1−Q)=h(a)/(4a(1−a))→∞ as a→0⁺. Consequently no fixed p>0 makes Q^p≤J universal, and no function F with F(1)=1 that is locally Lipschitz at one makes F(Q)≤J universal. The logarithmic entropy deficit near orthogonal supports causes this obstruction. The upper inequality QJS₂≤QTD and the metric assertion for √QTD are not addressed.

## References

- Truth anchor: `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.QJS2`
- Truth anchor: `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.QTD`
- Truth anchor: `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.claim`
- Truth anchor: `D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.result`
- Dependency: [D5/S3/Divergence/CoherenceL1RelativeEntropyBound](CoherenceL1RelativeEntropyBound.md)
