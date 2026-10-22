# Normalized Bessel functions

## Abstract

The normalized Bessel series and the conjectured Redheffer lower bound.

**Definition 1.1 (The normalized series).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Defs.nbessel`

*Formalization.* `D5/S3/Analytic/BesselRedheffer/Defs.nbessel` (`✓ std3`).

*Citation.* Á. Baricz and K. Mehrez (2018). *Redheffer type bounds for Bessel and modified Bessel functions of the first kind*. DOI: [10.1007/s00010-018-0545-8](https://doi.org/10.1007/s00010-018-0545-8). URL: <https://arxiv.org/abs/1701.08446>.

*Commentary.*

For real order nu and argument x, the function is the sum of (-x squared/4) to the power k divided by k factorial and the rising factorial of nu+1 of order k.

**Definition 1.2 (The first positive zero).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Defs.firstZero`

*Formalization.* `D5/S3/Analytic/BesselRedheffer/Defs.firstZero` (`✓ std3`).

*Citation.* Á. Baricz and K. Mehrez (2018). *Redheffer type bounds for Bessel and modified Bessel functions of the first kind*. DOI: [10.1007/s00010-018-0545-8](https://doi.org/10.1007/s00010-018-0545-8). URL: <https://arxiv.org/abs/1701.08446>.

*Commentary.*

The first zero is the infimum of the set of positive real arguments where the normalized series vanishes. Existence and positivity require separate proofs.

**Definition 1.3 (The conjectured lower bound).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Defs.claim`

*Formalization.* `D5/S3/Analytic/BesselRedheffer/Defs.claim` (`✓ std3`).

*Citation.* Á. Baricz and K. Mehrez (2018). *Redheffer type bounds for Bessel and modified Bessel functions of the first kind*. DOI: [10.1007/s00010-018-0545-8](https://doi.org/10.1007/s00010-018-0545-8). URL: <https://arxiv.org/abs/1701.08446>.

*Commentary.*

For every nu greater than -1 and every real x with absolute value less than the first positive zero j, the real power of j squared divided by j squared minus x squared, with exponent j squared divided by 4(nu+1)(nu+2), is at most the ratio of the normalized series of orders nu+1 and nu.

## References

- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Defs.claim`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Defs.firstZero`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Defs.nbessel`
