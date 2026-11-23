# Actual Leech orbifold norm-two relative BRST cohomology

## Abstract

The actual norm-two relative BRST quotient is one-dimensional in ghost degree one.

For each integral ghost degree, the cochains are the corresponding eigenspace of ghost number on the relative shell. The differential restricts the actual BRST charge Q. Cohomology quotients its kernel by the range of the preceding differential, which lands in the kernel by Q² = 0.

**Definition 1.1 (Degree-one equivalence).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomologyOne`

*Formalization.* `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomologyOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In degree one the coefficient ρ of a cycle induces a complex linear equivalence from the quotient to ℂ.

**Theorem 1.2 (Value on the distinguished class).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomologyOne_psiClass`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomologyOne_psiClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence sends the class of the relative generator ψ to 1.

**Theorem 1.3 (Nonzero cohomology class).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.psiClass_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.psiClass_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of ψ is nonzero in the degree-one quotient.

**Theorem 1.4 (Vanishing in all other degrees).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomology_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomology_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer q different from one, the degree-q relative BRST quotient is a subsingleton.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomologyOne`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomologyOne_psiClass`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.cohomology_vanishes`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.psiClass_ne_zero`
- Dependency: [D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo](ActualLeechOrbifoldRelativeNormTwo.md)
