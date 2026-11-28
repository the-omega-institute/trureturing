# Local Chi-Square Subadditivity for Symmetric Channels

## Abstract

Uniform local chi-square subadditivity for finite symmetric channels observing one input.

**Theorem 1.1 (A constant independent of the output alphabet sizes).**

$$\forall q: \mathbb{N}, 2\le q \Rightarrow \exists A: \mathbb{R}, 0<A \land \forall Y: \operatorname{Type}, \forall Z: \operatorname{Type}, [\operatorname{Fintype}\left(Y\right)] [\operatorname{Fintype}\left(Z\right)], \forall P: \operatorname{FMSChannel}\left(\operatorname{Fin}\left(q\right), Y\right), \forall Q: \operatorname{FMSChannel}\left(\operatorname{Fin}\left(q\right), Z\right), \forall e: \mathbb{R}, 0<e \Rightarrow C_{2}(P)\le e \Rightarrow C_{2}(\operatorname{star}\left(P, Q\right))\le (1+A e^{\frac{1}{5}}) (C_{2}(P)+C_{2}(Q))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/PottsLocalSubadditivity.fully_symmetric_fusion_bound` (`✓ std3`). ∎

*Citation.* Yuzhou Gu and Yury Polyanskiy (2023). *Uniqueness of BP fixed point for the Potts model and applications to community detection*. DOI: [10.48550/arXiv.2303.14688](https://doi.org/10.48550/arXiv.2303.14688). URL: <https://arxiv.org/html/2303.14688v2>.

*Commentary.*

The input is uniform on Fin(q), with q at least two. An FMSChannel is a nonnegative real row-stochastic table P(i,y), together with a group homomorphism from input permutations to output permutations preserving its entries under the simultaneous action. The output alphabets Y and Z are arbitrary finite types. The variable e in the formula is a positive real error parameter.

Write m_P(y) = q⁻¹ Σ_i P(i,y) and C₂(P) = q⁻¹ Σ_y (Σ_i P(i,y)²)/m_P(y) − 1. Real division gives 0/0 = 0. A zero output mass forces every entry in that column to be zero. The posterior on a zero column is assigned the uniform distribution; its weighted contribution remains zero. Thus zero entries, zero columns and redundant output symbols are included.

The channel star(P,Q) has table P(i,y)Q(i,z). Its two outputs are conditionally independent given the same input i. The product of the two output permutation actions certifies its symmetry. Its capacity equals the finite posterior-mixture fusion expression, including pairs of posteriors with zero overlap.

For a posterior p, the quadratic defect is q Σ_i p(i)² − 1. Permutation averaging cancels the first variation in the rational fusion expression. A centered sum of squares bounds the remaining overlap, giving a local square-root estimate. Splitting posterior mixtures at defect t² when their mean defect is at most t⁵ gives the fifth-root error. The choice A = 8q⁴ + q is positive and independent of both output alphabet sizes.

This is the finite-output form of Gu and Polyanskiy's local subadditivity estimate (arXiv:2303.14688v2, Lemma 20; Appendix D.1, Lemma 35). It supplies a bound for combining weak symmetric observations. The broader conjectures on uniqueness, boundary irrelevance and global stability of belief propagation above the Kesten–Stigum threshold concern iterated tree dynamics and are separate conclusions.

## References

- Truth anchor: `D5/S3/Divergence/PottsLocalSubadditivity.fully_symmetric_fusion_bound`
