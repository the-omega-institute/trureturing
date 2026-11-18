# Signed Candidates on the Complex Source Disk

## Abstract

Signed Candidates on the Complex Source Disk

Fix complex u,v and put R=min(1-norm(u),1-norm(v)). On the disk norm(z)<R, the literal signed J and T formulas at r=z^2 are holomorphic. Source amplitudes use their actual amplitude derivatives. The E denominator uses the stronger norm(u)+sqrt(norm(r))<1 bound, which becomes exactly norm(u)+norm(z)<1; the W branches retain positive real part, and the correction uses the original nonvanishing period. No square-root branch substitution for z is used.

**Theorem 1.1 (norm_lt_sourceRadius_iff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The disk condition is exactly the conjunction of the two original source norm inequalities.

**Theorem 1.2 (sourceRadius_pos).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common disk has positive radius whenever both source coordinates have norm less than one.

**Theorem 1.3 (sourceRadius_le_one).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common source disk has radius at most one.

**Theorem 1.4 (candidate_square_analyticOnNhd).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either kernel selector and every sign pair, the literal signed candidate composed with z squared is analytic on a neighborhood of every point in the original common source disk.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource](../Signed/CandidateSource.md)
