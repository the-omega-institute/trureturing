# A family of strict counterexamples

## Abstract

Counterexamples to the normalized Bessel Redheffer lower bound.

**Theorem 1.1 (Every order at least thirty).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Result.failure_family`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Result.failure_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Á. Baricz and K. Mehrez (2018). *Redheffer type bounds for Bessel and modified Bessel functions of the first kind*. DOI: [10.1007/s00010-018-0545-8](https://doi.org/10.1007/s00010-018-0545-8). URL: <https://arxiv.org/abs/1701.08446>.

*Commentary.*

For each real order nu at least 30, there is a positive x below the first positive zero of the normalized Bessel function such that the proposed lower bound is strictly greater than the ratio. The first-zero theorem supplies positivity and the energy upper bound. The local comparison supplies a positive interval of strict violations, from which half the interval radius is chosen.

**Theorem 1.2 (The universal lower bound is false).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/baricz-mehrez-2018-bessel-redheffer-lower-bound` (refuted) by `D5/S3/Analytic/BesselRedheffer/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baricz-mehrez-2018-bessel-redheffer-lower-bound","declaration_gid":"D5/S3/Analytic/BesselRedheffer/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Á. Baricz and K. Mehrez (2018). *Redheffer type bounds for Bessel and modified Bessel functions of the first kind*. DOI: [10.1007/s00010-018-0545-8](https://doi.org/10.1007/s00010-018-0545-8). URL: <https://arxiv.org/abs/1701.08446>.

*Commentary.*

The pinned claim quantifies over every real order greater than -1 and every real x of absolute value below the first positive zero. Specializing the counterexample family to order 30 gives an admissible positive x and contradicts the claimed inequality. The series definition, the first zero defined as an infimum, and the real-power exponent are those of the pinned claim.

## References

- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Result.failure_family`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Result.result`
- Dependency: [D5/S3/Analytic/BesselRedheffer/Expansion](Expansion.md)
- Dependency: [D5/S3/Analytic/BesselRedheffer/FirstZero](FirstZero.md)
