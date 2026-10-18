# Opposite matching minimizes expanding diagonal products

## Abstract

Opposite matching minimizes expanding diagonal products.

**Theorem 1.1 (Subset products control a diagonal gauge).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingDiagonal.N_diagonal_subsetProducts_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingDiagonal.N_diagonal_subsetProducts_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x and y be nonnegative real vectors with y decreasing. Suppose that for every coordinate subset I, the product of x over I is at most the product of the |I| first coordinates of y. Then N(diag(x))≤N(diag(y)) for every unitarily invariant norm N. Sorting x converts the subset bounds to weak log-majorization; power-sum comparison gives weak majorization and hence the gauge inequality.

**Theorem 1.2 (A single minimizing permutation for all expanding factors).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingDiagonal.exists_permutation_expanding_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingDiagonal.exists_permutation_expanding_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative real vectors a and b and a unitarily invariant norm N, there exists a permutation σ such that N(diag(a)Pσdiag(b))≤N(diag(a)Tdiag(b)) for every complex square T satisfying T*T−I positive semidefinite. For positive weights, the lower Gelfand–Naimark inequality on arbitrary index subsets compares the opposite matching a↓ᵢb↑ᵢ with the singular values of diag(a)Tdiag(b). Replacing both weights by their sums with a positive ε and taking ε to zero extends the same permutation to zero weights.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingDiagonal.N_diagonal_subsetProducts_le`
- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingDiagonal.exists_permutation_expanding_lower_bound`
- Dependency: [D5/S3/Quantum/Schatten/DiagonalSingularValues](DiagonalSingularValues.md)
- Dependency: [D5/S3/Quantum/Schatten/ExpandingGram](ExpandingGram.md)
- Dependency: [D5/S3/Quantum/Schatten/LowerGelfandNaimark](LowerGelfandNaimark.md)
- Dependency: [D5/S3/Quantum/Schatten/PowerMajorization](PowerMajorization.md)
- Dependency: [D5/S3/Quantum/Schatten/UINormContinuity](UINormContinuity.md)
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](UnitarilyInvariantNorm.md)
