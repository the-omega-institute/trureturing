# The full charged correction commutes with source partial derivatives

## Abstract

The full charged correction commutes with source partial derivatives

The operator is exactly the original Corr. Its correctionWord has the original singletonPolynomial, pairPolynomial and pairDerivation; no neutral substitution or alternative correction map is used.

**Theorem 1.1 (The full charged correction commutes with source partial derivatives).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The source derivative at any ordinary index commutes coefficientwise through Corr for every charge, polynomial and correction shift. The proof establishes partial_pairDerivation and partial_insertion on the actual correction polynomial, retaining the charged singleton and pair constants, and then passes through optionEquivLeft.

The singleton coefficient at source weight one is the actual negative charge pairing divided by two. The pair coefficients retain pairScalar and both halfBinomial factors. They are constants for the source partial derivative, not deleted terms. Corr_neutralPolynomialMode consumes this result with the original frequency-weighted derivative and the actual charge zero mode.

The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.

This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
