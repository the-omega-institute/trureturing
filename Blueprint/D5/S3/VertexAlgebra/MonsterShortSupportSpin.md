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

**Definition 1.3 (Public short-support weight).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.shortWeight`

*Formalization.* `D5/S3/VertexAlgebra/MonsterShortSupportSpin.shortWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. J. MacWilliams and N. J. A. Sloane (1977). *The Theory of Error-Correcting Codes*. URL: <https://archive.org/details/theoryoferrorcor00macw>.

*Commentary.*

The existing unique representative theorem remains in MonsterShortSupport; this declaration supplies its public weight expression.

**Theorem 1.4 (Explicit six-section expansion).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.sixMap_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupportSpin.sixMap_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

This coordinate expansion is the public interface used by the finite full-map quadratic proof.

**Theorem 1.5 (All-ones six-section relation).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.sixMap_allOnes_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupportSpin.sixMap_allOnes_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

The seven-section relation identifies the all-ones six-section sum with the seventh nonzero ground section.

**Theorem 1.6 (Quadratic parity of the full seven-section map).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_fullMap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_fullMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

The proof sums over the selected support, inducts on its cardinality, and uses the ground-section value and distinct-section polar pairing. It proves the binomial parity formula in F_2. This is still a finite label theorem and does not construct VOA modules, fusion intertwiners, OPE coefficients, or conformal weights.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_fullMap`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.labelQuadratic_groundSection_polar`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.shortWeight`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.sixMap_allOnes_explicit`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupportSpin.sixMap_explicit`
- Dependency: [D5/S3/VertexAlgebra/MonsterShortSupport](MonsterShortSupport.md)
