# Multiplication through the charged correction

## Abstract

Multiplication through the charged correction

The correction field is the original charged correctedPolynomial. Multiplication by a source variable adds its physical normal insertion, the charged singleton term and the pair contractions over every source index.

**Theorem 1.1 (Corrected polynomial multiplication).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeed.correctedPolynomial_X_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeed.correctedPolynomial_X_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The pair sum is supported on the variables of the input polynomial. Partial differentiation removes labelled occurrences with their actual multiplicities. The proof evaluates the original correctionLift insertion and transports every correction shift through normalInsertion. The resulting identity supplies the physical current seed.

The original singletonPolynomial and pairPolynomial coefficients remain unchanged. The field evaluation is coefficient extraction followed by the existing normalPolynomial and even correction shifts; it is not a replacement state-field map.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeed.correctedPolynomial_X_mul`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStateCurrentCommutator](LatticeHalfFockAllStateCurrentCommutator.md)
