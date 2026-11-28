# Bilinear Chi-Square Fusion for Finite Channels

## Abstract

A uniform bilinear chi-square bound for finite observations of a common hidden input.

**Theorem 1.1 (Arbitrary channel tables and finite output alphabets).**

$$\forall I: \operatorname{Type}, \forall Y: \operatorname{Type}, \forall Z: \operatorname{Type}, [\operatorname{Fintype}\left(I\right)] [\operatorname{Nonempty}\left(I\right)] [\operatorname{Fintype}\left(Y\right)] [\operatorname{Fintype}\left(Z\right)], \forall P: I \to Y \to \mathbb{R}, \forall Q: I \to Z \to \mathbb{R}, \operatorname{Nonnegative}\left(P\right) \Rightarrow \operatorname{Nonnegative}\left(Q\right) \Rightarrow \operatorname{RowStochastic}\left(P\right) \Rightarrow \operatorname{RowStochastic}\left(Q\right) \Rightarrow C_{2}(\operatorname{star}\left(P, Q\right))\le C_{2}(P)+C_{2}(Q)+32 \operatorname{card}\left(I\right) C_{2}(P) C_{2}(Q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ChiSquareBilinearFusion.bilinear_fusion_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuzhou Gu and Yury Polyanskiy (2023). *Uniqueness of BP fixed point for the Potts model and applications to community detection*. DOI: [10.48550/arXiv.2303.14688](https://doi.org/10.48550/arXiv.2303.14688). URL: <https://arxiv.org/html/2303.14688v2>.

*Commentary.*

I is any nonempty finite input type, n = |I|, and the hidden input is uniform on I. Y and Z are arbitrary finite output types. Nonnegative(P) means P(i,y) ≥ 0 for every input and output, and RowStochastic(P) means Σ_y P(i,y) = 1 for each input; Q has the corresponding conditions. No permutation symmetry is required.

The output margin is m_P(y) = n⁻¹ Σ_i P(i,y), and the capacity is C₂(P) = n⁻¹ Σ_y (Σ_i P(i,y)²)/m_P(y) − 1. The product table is star(P,Q)(i,(y,z)) = P(i,y)Q(i,z). Thus the outputs are conditionally independent given the same input. Real division retains 0/0 = 0. Zero entries, zero output columns, redundant symbols and zero overlap are all included.

Write E for uniform input averaging. The likelihood x_y(i) is P(i,y)/m_P(y) on a positive-mass column and one on a zero column. Its mean is one, its range is [0,n], and Σ_y m_P(y)x_y(i) = 1 for each input i. The zero-column convention has zero weight and satisfies the exact reconstruction m_P(y)x_y(i) = P(i,y). The same identities hold for the likelihood r of Q.

For a = x − 1 and b = r − 1, put A = E(a²), B = E(b²), c = E(ab), d = E(a²b), e = E(ab²), and H = E(x²r²)/E(xr) − 1. The rational estimate is H ≤ A + B + (3 − A − B)c + 2d + 2e + 32nAB. On 1 + c ≥ 1/2 an exact numerator expansion and Cauchy–Schwarz control its remainder. On the complementary region, E|ab| ≥ 1/2 forces AB ≥ 1/4; the zero-inclusive bound H ≤ n(1+c) − 1 controls the small denominator.

Averaging over the two output-margin weights cancels the terms c, Ac, Bc, d and e by coordinate calibration. The average of AB factors into the two capacities. These auxiliary product weights do not replace the actual joint output margin, which is m_P(y)m_Q(z)E(x_y r_z). The exact ratio reconstruction gives the stated bound, independent of both output cardinalities. In particular, for n ≥ 2 one may take the positive coefficient K_n = 32n.

This finite-channel estimate is an ingredient for information combining and asymmetric noisy observations. The research anchor is the Gu–Polyanskiy Potts-model question on BP uniqueness, boundary irrelevance and global stability above the Kesten–Stigum threshold (arXiv:2303.14688v2, Appendix H). This theorem does not establish convergence of an iterated tree recursion, the conjectured global stability, infinite output extensions, an optimal coefficient, or mathematical novelty.

## References

- Truth anchor: `D5/S3/Divergence/ChiSquareBilinearFusion.bilinear_fusion_bound`
