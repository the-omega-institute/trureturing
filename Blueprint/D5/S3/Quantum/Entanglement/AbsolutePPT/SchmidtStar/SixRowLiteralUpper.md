# SixRowLiteralUpper

## Abstract

Literal six-row purity upper bound and exact original ordered equality

**Theorem 1.1 (ordered literal upper bound and equality).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.literal_upper_and_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.literal_upper_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 23, an antitone nonnegative unit-mass spectrum l with APPT of its actual e-labelled diagonal has sum l_i squared at most theta(n), with equality iff the entire original l equals centralSpectrum(n). Extraction and concentration use identical original boundary moments. Equality is conditional on the stated premises; no concentrated vector is assumed APPT.

**Theorem 1.2 (arbitrary APPT density upper bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.density_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.density_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 23 and an arbitrary PSD trace-one APPT complex matrix on Fin 6 times Fin n, the real trace of its square is at most theta(n): 6/(35n) for even n and 6(35n+2)/(35n+1)^2 for odd n. The existing spectral reduction yields one ordered spectrum, APPT of its labelled diagonal and the equality of purities used for the transfer.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.density_upper`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.literal_upper_and_equality`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity](../QuadbitQuintitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowConcentration](SixRowConcentration.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction](SixRowPhysicalExtraction.md)
