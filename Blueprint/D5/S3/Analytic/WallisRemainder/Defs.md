# Wallis remainder functions

## Abstract

The Wallis gamma ratio and three normalized remainder functions.

**Definition 1.1 (The gamma ratio).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Defs.wallisB`

*Formalization.* `D5/S3/Analytic/WallisRemainder/Defs.wallisB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x, B(x) is the square root of x times Gamma(x+1/2), divided by Gamma(x+1).

**Definition 1.2 (The reciprocal remainder).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Defs.mu`

*Formalization.* `D5/S3/Analytic/WallisRemainder/Defs.mu` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x, mu(x) is minus x squared minus the reciprocal of 24 plus (3/x) times the reciprocal of log B(x).

**Definition 1.3 (The first normalized difference).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Defs.theta`

*Formalization.* `D5/S3/Analytic/WallisRemainder/Defs.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x, theta(x) is (23040/31) times x to the fifth power times the sum of 3x/(24x squared+1) and log B(x).

**Definition 1.4 (The second normalized difference).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Defs.chi`

*Formalization.* `D5/S3/Analytic/WallisRemainder/Defs.chi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x, chi(x) is (358400/257) times x to the seventh power times the sum of (120x squared+31)/(96x(10x squared+3)) and log B(x).

**Definition 1.5 (The monotonicity assertion).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Defs.claim`

*Formalization.* `D5/S3/Analytic/WallisRemainder/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the positive real ray, log B(x) and the inner reciprocal denominator of mu(x) are nonzero; mu and chi are strictly increasing and theta is strictly decreasing.

## References

- Truth anchor: `D5/S3/Analytic/WallisRemainder/Defs.chi`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Defs.claim`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Defs.mu`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Defs.theta`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Defs.wallisB`
