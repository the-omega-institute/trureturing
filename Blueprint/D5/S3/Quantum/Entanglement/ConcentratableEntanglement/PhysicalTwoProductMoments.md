# Spectral moments for coherent two-product amplitudes

## Abstract

All positive real moments of the actual reduced states of a coherent sum of two products have a two-value spectral formula.

**Theorem 1.1 (Exact real power traces and a normalization bound).**

$$\forall K \in \mathbb{R},\; \forall Q \in NonzeroTwoProductData,\; (0 < K) \Rightarrow ((\forall i \in \operatorname{Sites}\left(Q\right),\; \operatorname{s}\left(Q, i\right) \le 1) \land ((\operatorname{PhaseBound}\left(Q\right) \le \operatorname{N}\left(Q\right)) \land (\forall U \in \operatorname{Subsets}\left(\operatorname{Sites}\left(Q\right)\right),\; \operatorname{TrPower}\left(Q, K, U\right) = (\frac{1 + \operatorname{t}\left(Q, U\right)}{2})^{K} + (\frac{1 - \operatorname{t}\left(Q, U\right)}{2})^{K})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConcentratableEntanglement/PhysicalTwoProductMoments.physical_two_product_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoguang Wang (2002). *Bipartite entangled non-orthogonal states*. DOI: [10.1088/0305-4470/35/1/313](https://doi.org/10.1088/0305-4470/35/1/313). URL: <https://arxiv.org/abs/quant-ph/0102011v5>.

*Commentary.*

A datum Ψ consists of a finite site set, a finite configuration type at each site, two local complex unit vectors per site, and complex coefficients a and b. The literal amplitude is a times the product of the first vectors plus b times the product of the second vectors. Its nonzero squared norm is N. The actual reduction ρ(U) sums the literal outer product over configurations on the complement and divides by N. The power in each trace is the real functional calculus on the reduced matrix.

Write s(i) for the local squared overlap magnitude; the theorem proves s(i) ≤ 1. The normalization bound states N ≥ 2|a b|(1 − sqrt(product of s(i) over all sites)); this allows destructive phase interference. For each U, d(U) equals |a b|²/N² times one minus the overlap product on U times one minus the overlap product on its complement, and t(U) = sqrt(1 − 4d(U)). The finite Gram determinant and rank-two compression give the stated moment even when one spectral value vanishes. The two-value calculation is the grouped-cut form of Wang’s bipartite concurrence formula; here it is attached to the actual finite partial trace and extended to all positive real trace powers.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglement/PhysicalTwoProductMoments.physical_two_product_moments`
