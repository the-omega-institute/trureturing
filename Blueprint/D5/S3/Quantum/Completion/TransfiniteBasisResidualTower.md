# Transfinite Hilbert-Basis Residual Tower

## Abstract

An initially indexed infinite Hilbert basis determines successor splittings, exact limit stages, full-size proper residuals, and a zero terminal residual.

**Theorem 1.1 (Initially indexed bases split every residual stage).**

$$\begin{gathered}\forall K, H, I, b,\\{}\operatorname{Hilbert}\left(K, H\right), \operatorname{InfiniteInitialWellOrder}\left(I\right), \operatorname{HilbertBasis}\left(b, I, K, H\right),\\{}(\forall i\in I, \operatorname{Residual}\left(b, \operatorname{Iio}\left(i\right)\right) = \operatorname{DirectSum}\left(\operatorname{span}\left(K, b_{i}\right), \operatorname{Residual}\left(b, \operatorname{Iic}\left(i\right)\right)\right) \land \operatorname{Orthogonal}\left(\operatorname{span}\left(K, b_{i}\right), \operatorname{Residual}\left(b, \operatorname{Iic}\left(i\right)\right)\right)) \land\\{}((\forall i\in I, \operatorname{Limit}\left(i\right) \Rightarrow \operatorname{Prefix}\left(b, \operatorname{Iio}\left(i\right)\right) = \operatorname{ClosedSup}\left(\operatorname{Prefix}\left(b, \operatorname{Iio}\left(j\right)\right)_{j<i}\right) \land \operatorname{Residual}\left(b, \operatorname{Iio}\left(i\right)\right) = \operatorname{Inf}\left(\operatorname{Residual}\left(b, \operatorname{Iio}\left(j\right)\right)_{j<i}\right)) \land\\{}\operatorname{Prefix}\left(b, I\right) = \operatorname{ClosedSup}\left(\operatorname{Prefix}\left(b, \operatorname{Iio}\left(j\right)\right)_{j\in I}\right) \land \operatorname{Residual}\left(b, I\right) = \operatorname{Inf}\left(\operatorname{Residual}\left(b, \operatorname{Iio}\left(j\right)\right)_{j\in I}\right)) \land\\{}(\forall i\in I, \operatorname{Card}\left(I \setminus \operatorname{Iio}\left(i\right)\right) = \operatorname{Card}\left(I\right) \land (\forall j\in I \setminus \operatorname{Iio}\left(i\right), E_{i}(t_{j}) = b(epsilon_{i}(j)))) \land\\{}\operatorname{Residual}\left(b, I\right) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/TransfiniteBasisResidualTower.transfinite_basis_residual_tower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hilbert basis indexed by an infinite initial well-order, the prefix at a set of indices is its closed linear span and the residual is the orthogonal complement of that prefix.

A successor stage splits off the current basis line orthogonally. At a limit index, the prefix is the closed supremum of earlier prefixes and the residual is their intersection.

Every proper initial segment leaves an index complement of the original cardinality. The displayed isometry sends each named tail vector to its reindexed ambient basis vector, while the full-index residual is zero.

## References

- Truth anchor: `D5/S3/Quantum/Completion/TransfiniteBasisResidualTower.transfinite_basis_residual_tower`
