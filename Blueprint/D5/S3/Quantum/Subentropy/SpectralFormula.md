# The simple-spectrum subentropy formula

## Abstract

The determinant integral agrees with the finite spectral subentropy formula for distinct positive probabilities.

**Definition 1.1 (Spectral residue coefficients).**

Lean statement: `D5/S3/Quantum/Subentropy/SpectralFormula.spectralCoefficient`

*Formalization.* `D5/S3/Quantum/Subentropy/SpectralFormula.spectralCoefficient` (`✓ std3`).

*Citation.* Richard Jozsa, Daniel Robb, William K. Wootters (1994). *Lower bound for accessible information in quantum mechanics*. DOI: [10.1103/PhysRevA.49.668](https://doi.org/10.1103/PhysRevA.49.668). URL: <https://doi.org/10.1103/PhysRevA.49.668>.

*Commentary.*

For a real vector p on a finite type of cardinality N, the coefficient at i is p_i to exponent N divided by the product of p_i−p_j over all j distinct from i. The formula becomes the classical subentropy residue on positive distinct probability vectors. The total Lean definition also exists at coincident coordinates, but its zero-denominator convention does not define the paper's continuous extension.

**Theorem 1.2 (Agreement with the finite spectral formula).**

Lean statement: `D5/S3/Quantum/Subentropy/SpectralFormula.matrixSubentropy_diagonal_eq_distinct_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/SpectralFormula.matrixSubentropy_diagonal_eq_distinct_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For every finite type with decidable equality, every strictly positive real vector p with sum one and injective coordinates satisfies the following identity: the determinant integral of diagonal p equals the negative sum, over i, of p_i to exponent N times log p_i divided by the product of p_i−p_j over j distinct from i. N is the cardinality of the entire index type. Injectivity means pairwise distinct entries; there is no ordering hypothesis. The logarithm is natural.

The finite spectral formula is attributed to the original subentropy literature and the later properties paper. The determinant-integral representation and its proof of agreement are repository derivations. Lagrange interpolation is applied to the degree-below-N polynomial formed by subtracting X to exponent N from the product of X+p_i. Evaluating at the distinct nodes −p_i gives the residue coefficients. The coefficient of X to exponent N−1 proves that their sum is one.

Dividing the interpolated identity by the nonzero product of t+p_i gives the kernel as a finite weighted sum of reciprocal differences 1/(t+p_i)−1/(t+1). Each difference is integrated as a single integrable function; its two reciprocal terms are not separated. Strict positivity and total mass one give 0<p_i≤1, so the existing reciprocal-difference integral applies to each coefficient. Negative residue coefficients are allowed, and the finite integral interchange uses integrability rather than a positivity assumption on those coefficients.

This theorem covers positive simple spectra and does not evaluate the quotient at repeated or zero entries. DensityKernel proves continuity of the determinant integral on positive trace-one matrices, including the boundary. Positive simple probability vectors are dense: mix an arbitrary probability vector p with a strictly positive distinct vector q, and choose positive mixing parameters tending to zero while avoiding the finitely many values at which a pair of coordinates coincides. Every coordinate is positive, and each pair can coincide at at most one parameter because q has distinct coordinates. Thus the simple-spectrum identity and continuity determine the continuous extension. StrongSubadditivityRefutation proves the density and uniqueness bridge as a consumed private theorem: ordered positive perturbations converge in a fixed eigenbasis, and continuity identifies every invariant spectral family with the determinant integral. Source metadata boundaries remain in the cited library notes.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/SpectralFormula.matrixSubentropy_diagonal_eq_distinct_formula`
- Truth anchor: `D5/S3/Quantum/Subentropy/SpectralFormula.spectralCoefficient`
- Dependency: [D5/S3/Quantum/Subentropy/Basic](Basic.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](UniformIntegrals.md)
