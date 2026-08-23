# Complete Context Tomography

## Abstract

A complete complementary context family spans every traceless Hermitian matrix.

**Theorem 1.1 (Complete context tomography).**

$$\operatorname{ContextFamily}(C, d) \land \operatorname{ComplementaryOverlap}(C, d) \Rightarrow\\\operatorname{UniqueCenteredDiagonalDecomposition}(C, d) \land \\\operatorname{ZeroInvisibleTracelessResidual}(C, d) \land \\\operatorname{ProbabilityUniqueness}(C, d).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CompleteContextTomography.complete_context_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A context family consists of d+1 canonical normalized rank-one projective contexts in dimension d. Its public overlap law says that projectors in one context have Kronecker trace overlap, while projectors in distinct contexts have constant inverse-dimension overlap.

The identity and all projector differences form a basis of the full complex matrix space. The proof derives independence from the overlap law, counts the vectors against the matrix finrank, and then specializes the resulting coordinates to real centered coefficients for Hermitian traceless matrices.

The displayed theorem keeps all three source consequences public: unique centered diagonal decomposition, zero common invisible traceless residual, and uniqueness of a matrix from every context probability. No completeness or reconstruction property is assumed as a hidden premise.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/CompleteContextTomography.complete_context_tomography`
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](RankOneContextCommutator.md)
