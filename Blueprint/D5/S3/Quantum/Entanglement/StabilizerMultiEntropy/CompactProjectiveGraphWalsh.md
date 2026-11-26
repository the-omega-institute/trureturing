# Characteristic cancellation for compact graph states

## Abstract

The actual graph-state full Walsh coefficient is a binary projective characteristic product.

**Theorem 1.1 (The full-system Walsh factor of the compact projective graph).**

$$\forall K \in \mathbb{R},\; (1 < K) \Rightarrow ((\forall n \in \mathbb{N},\; \operatorname{W}\left(K, n\right) = \operatorname{ProjectiveFactor}\left(\operatorname{q}\left(K\right), n\right)) \land (\forall m \in \mathbb{N},\; (\operatorname{OpenDyadicBand}\left(\operatorname{q}\left(K\right), m\right)) \Rightarrow (\operatorname{W}\left(K, m + 1\right) < 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/CompactProjectiveGraphWalsh.compact_projective_walsh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sang-il Oum (2005). *Rank-width and vertex-minors*. DOI: [10.1016/j.jctb.2005.03.003](https://doi.org/10.1016/j.jctb.2005.03.003). URL: <https://mathsci.kaist.ac.kr/~sangil/pdf/vertexminor.pdf>.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

For each n, use every nonzero vector over the binary field in dimension n + 1 and one parallel copy of a basis vector. The fundamental graph of the resulting systematic chart has exactly 2^(n + 1) sites, including the basis sites but no ancillary coordinate or zero-vector sites. The observable is the normalized reduced graph-state matrix's actual real power trace at each subsystem. W is its alternating full-system sum; its candidate probability mass is W divided by 2 to the number of sites.

Oum's Proposition 3.1 expresses a cut rank as the sum of the two restriction ranks minus total rank in this normalization. On a cut with neither side spanning, the residual is an exact product of the two rank defects in the powers. One cut side spans here because two proper binary subspaces cannot cover all points. Under this condition the cut moment is the sum of the two restriction-rank powers minus the full-rank power. Complementing the mask aligns the even full-system signs and the constant cancels. Grouping the two parallel copies gives the three weights -1, -1, +1, so their total agrees with a single copy. The resulting signed sum is the binary projective characteristic product, namely twice the product of (1 − 2^j/q) over 0 ≤ j ≤ n.

Let q be 2^(K-1). For the graph of dimension m + 2, only the last product factor is negative when 2^m < q < 2^(m+1). The full-system Walsh numerator is strictly negative on this entire band. This does not claim that every graph fails at noninteger order, or that this size is optimal for every band.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/CompactProjectiveGraphWalsh.compact_projective_walsh`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial](BinaryProjectiveRankPolynomial.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement](GraphStateConcentratableEntanglement.md)
