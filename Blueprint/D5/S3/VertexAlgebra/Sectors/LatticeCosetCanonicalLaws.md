# Actual conformal translations of full Hahn fields

## Abstract

LatticeCosetCanonicalLaws

**Theorem 1.1 (projection_translation).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.projection_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.projection_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive-definite original D, arbitrary external rank and B, any complex H satisfying both H*gramComplex=1 and gramComplex*H=1, every external d and every state v in the full ambient carrier, projection_d(Tambient v)=moduleL D (B*d) H (-1)(projection_d v). This includes off-d charge fibers. Here arbitrary polynomial derivation and projected charge transport prove the identity, which supplies the target derivative identity.

**Theorem 1.2 (translation_injection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.translation_injection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.translation_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same inverse and positivity hypotheses, ambient translation of every injected original v is its injected actual moduleL(-1) plus multiplication by the transverse charge oscillator. The transverse summand is retained. This decomposes both integer derivative identities.

**Theorem 1.3 (source_derivative).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.source_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.source_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For those hypotheses, all a,b,u,v and every rational tau, mode of the canonical field on moduleL D (B*a) H (-1)u equals minus tau times its mode tau-1 on u, evaluated on v. Native source translation contributes +schur(b,a); subtracting it from the integer derivative supplies exactly the rational shift. Off-coset modes vanish on both sides. This is the exact Lawful.source identity.

**Theorem 1.4 (target_derivative).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.target_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.target_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For those hypotheses, all a,b,u,v and every rational tau, actual moduleL D (B*a+B*b) H (-1) acting on the field coefficient minus the coefficient on moduleL D (B*b) H (-1)v equals minus tau times the tau-1 coefficient. The transverse input correction is -schur(a,b), with the literal ordered sign. Off-coset families separately vanish. This is the exact Lawful.target identity.

Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.projection_translation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.source_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.target_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws.translation_injection`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalJacobi](LatticeCosetCanonicalJacobi.md)
