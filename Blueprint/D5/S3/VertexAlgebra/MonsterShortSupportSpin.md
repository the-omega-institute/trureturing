# Monster Short-Support Spin Data

## Abstract

Finite Monster labels carry a quadratic ground-section parity.

The label quadratic is defined independently of the seven-section map. Right-additivity identifies its value on a ground section with the diagonal sign, and the opposite law identifies the polar pairing of distinct nonzero sections.

**Theorem 1.1 (Ground-section quadratic value).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

This is a finite label theorem. It does not construct a VOA module, an intertwiner, an OPE coefficient, or a Monster action.

**Theorem 1.2 (Distinct-section polar pairing).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection_polar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection_polar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. J. MacWilliams and N. J. A. Sloane (1977). *The Theory of Error-Correcting Codes*. URL: <https://archive.org/details/theoryoferrorcor00macw>.

*Commentary.*

The proof consumes the IsSignTable opposite law, so the quadratic datum is not a renamed support predicate.

**Theorem 1.3 (Public unique short-support API).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.unique_short_support_public`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupportSpin.unique_short_support_public` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

This exposes the existing unique representative theorem under the public shortWeight name.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection_polar`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.unique_short_support_public`
- Dependency: [D5/S3/VertexAlgebra/MonsterShortSupport](MonsterShortSupport.md)
