# The Two-Basic-Open Cech Complex

## Abstract

The degree-zero Cech complex of two principal opens covering an affine scheme is a short exact complex of modules.

**Definition 1.1 (The concrete localization complex).**

Lean statement: `D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.twoBasicOpenCechComplex`

*Formalization.* `D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.twoBasicOpenCechComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The Stacks Project Authors (2026). *The Stacks project*. URL: <https://stacks.math.columbia.edu/tag/00EK>.

*Commentary.*

For a commutative ring R and elements f and g, the complex maps R diagonally to Away f times Away g. Its second map sends (x, y) to the image of x under awayToAwayRight minus the image of y under awayToAwayLeft in Away (f g).

**Theorem 1.2 (Short exactness under the covering condition).**

Lean statement: `D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.two_basic_open_cech_short_exact`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.two_basic_open_cech_short_exact` (`✓ std3`). ∎

*Citation.* The Stacks Project Authors (2026). *The Stacks project*. URL: <https://stacks.math.columbia.edu/tag/00EK>.

*Commentary.*

If f and g generate the unit ideal, the diagonal is injective and its image is the kernel of the overlap difference. The kernel argument uses the unique gluing theorem for localizations.

Surjectivity remains constructive. An overlap fraction with denominator (f g)^n is split using coefficients u and v with u f^n + v g^n = 1; the fractions (a v)/f^n and -(a u)/g^n form a preimage pair under the overlap-difference map.

Stacks tags 00EK and 01X9 supply the classical localization and affine-Cech mathematics. The exact ModuleCat object, chosen map orientation, and explicit powered-denominator proof are the repository's concrete Lean realization.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.twoBasicOpenCechComplex`
- Truth anchor: `D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.two_basic_open_cech_short_exact`
