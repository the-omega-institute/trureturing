# Finite transverse target action

## Abstract

LatticeCosetProjectedAction

**Definition 1.1 (polynomialMode).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.polynomialMode`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.polynomialMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any complex module V, any integer-indexed family A with values in V, and integer m, the complex linear polynomial functional sending monomial(j,z) to z times A(m-j). This is a finite coefficient sum, with no truncation hypothesis on A.

**Definition 1.2 (scalarTranslation).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.scalarTranslation`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.scalarTranslation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every external integral source a, the complex algebra homomorphism evaluating each transverse variable (j,k) at minus transversePair(a,j) times the polynomial variable to power k+1. It is the transverse part of native annihilation translation followed by longitudinal projection.

**Theorem 1.3 (projected_transverse_polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.projected_transverse_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.projected_transverse_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite original D with arbitrary finite rank and external rank, integral B, symmetric even-diagonal C, arbitrary external source a, arbitrary selected output sector d, every original source state u, every transverse polynomial h, integer mode m and every ambient target state v: project the complete native mode Y_E(J_a u)[m] applied to h(T)v. This equals polynomialMode at m, using the family t maps to P_d(Y_E(J_a u)[t]v), evaluated on scalarTranslation(a,h). Thus each inverse-power coefficient of the native transverse substitution shifts the complete longitudinal mode by its negative index. Every source descendant and every target polynomial is included. The proof inducts on h using the all-state transverse commutator; the sums are finite polynomial sums.

The native lattice conventions are those of Bakalov-Kac, math/0402315v1, section 4.1. The formula applies in particular to arbitrary longitudinal states multiplied by transverse creation coefficients, supplying the outer-source substitution needed in the two-source comparison. LatticeCosetOperatorCorrection combines this arbitrary-target action with the inner all-state creation expansion and exact binomial coefficient. No ambient positivity or scalar-cocycle replacement is used.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.polynomialMode`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.projected_transverse_polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction.scalarTranslation`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetFieldSeparation](LatticeCosetFieldSeparation.md)
