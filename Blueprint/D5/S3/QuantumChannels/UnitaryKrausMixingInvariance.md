# Unitary Kraus Mixing Invariance

## Abstract

A column-orthogonal change of finite Kraus generators leaves the induced channel independent of the branch labels used to present it.

**Definition 1.1 (Kraus generators are mixed by a complex coefficient matrix).**

$$\forall k \in \kappa,\ T_{k} = \sum_{j \in \iota} U_{kj} S_{j}.$$

*Formalization.* `D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.unitaryKrausMixing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite old-label set iota and new-label set kappa, the generator with new label k is the finite complex linear combination of the original generators whose coefficients are the k-th row of U.

**Theorem 1.2 (Column-orthogonal Kraus mixing preserves the channel).**

$$\forall \iota, \kappa, n, U, S, X,\ (\forall i, j \in \iota,\ \sum_{k \in \kappa} U_{ki} \operatorname{star}(U_{kj}) = \delta_{ij}) \Rightarrow \sum_{k \in \kappa} T_{k} X \operatorname{star}(T_{k}) = \sum_{j \in \iota} S_{j} X \operatorname{star}(S_{j}).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.unitary_kraus_mixing_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota, kappa, and n be finite types, let U be a complex coefficient matrix, let S be an iota-indexed family of complex n-by-n matrices, and let X be any complex n-by-n matrix. Assume the columns of U are orthonormal in the displayed component convention. Then mixing S by U leaves the sum of Kraus sandwiches exactly unchanged.

The coefficient convention sums U(k,i) times the conjugate of U(k,j). It is the complex conjugate of the usual column-inner-product identity with i and j exchanged, and hence has precisely the same content. Rectangular isometries are allowed, so the theorem also covers presentations with redundant new branch labels.

The proof distributes the adjoint through the finite linear combination, expands both finite sums, commutes their order, and uses column orthogonality to eliminate every cross term. The remaining diagonal terms are exactly the original Kraus sandwich sum.

This is the finite-dimensional matrix content of observer-gauge invariance. It does not assert that Clark bases exist, that arbitrary phase observers are related by such a matrix, or that an inner naming map has any further interpretation; those notions are not defined by the source atom as formal premises.

## References

- Truth anchor: `D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.unitaryKrausMixing`
- Truth anchor: `D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.unitary_kraus_mixing_invariance`
