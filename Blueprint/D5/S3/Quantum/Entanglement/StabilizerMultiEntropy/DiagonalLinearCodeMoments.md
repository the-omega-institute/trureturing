# Partial trace of a diagonal code is uniform on the projected code

## Abstract

Real-order subsystem moments of separable diagonal finite-field codes are controlled by the column ranks.

**Theorem 1.1 (The exact reduced-state power trace).**

$$\forall C \in \operatorname{FiniteFieldColumnConfiguration}\left(\right),\; \forall S \in \operatorname{Subsets}\left(\operatorname{Sites}\left(C\right)\right),\; \forall K \in \operatorname{PositiveReals}\left(\right),\; \operatorname{TrPower}\left(\operatorname{ActualMarginal}\left(C, S\right), K\right) = \operatorname{Pow}\left(\operatorname{AlphabetSize}\left(C\right), \operatorname{Mul}\left(\operatorname{Sub}\left(1, K\right), \operatorname{ColumnRank}\left(C, S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments.actual_column_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Choose a uniformly distributed linear functional on the message space and evaluate it on each column. The joint density matrix is explicitly a convex sum of products of computational-basis projectors. Tracing out the complement computes an ordinary coordinate pushforward. Nonempty fibers are translates of the kernel, and the image has dimension equal to the span of the selected columns by dual restriction.

The normalized marginal is a scaled projector of rank Q to the power r(S), so continuous functional calculus gives its actual real power trace. This covers arbitrary finite fields and K strictly positive. It does not assume a coverage law.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments.actual_column_moment`
