# Spectral variance of rank-one BKM outputs

## Abstract

Eigenbasis formulas and a conditioned variance bound for the finite BKM integral.

**Theorem 1.1 (Trace under unitary conjugation).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.trace_conjStarAlgAut_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSpectralVariance.trace_conjStarAlgAut_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating a finite complex matrix by a unitary preserves its complex trace.

**Definition 1.2 (Conjugation from the reference eigenbasis).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.fromEigenbasis`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSpectralVariance.fromEigenbasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eigenvector unitary of a positive definite reference takes a matrix in its eigenbasis back to the original coordinates by conjugation.

**Definition 1.3 (Linearity of the BKM integral).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omegaLinear`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSpectralVariance.omegaLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive definite reference, the eigenbasis formula expresses the BKM integral as multiplication by fixed scalars on entries. This gives a complex-linear map on the matrix algebra.

**Theorem 1.4 (Hermitian inputs and outputs).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the reference eigenbasis, the BKM integral multiplies each entry by the real logarithmic mean of its two eigenvalues. The symmetry of this multiplier preserves the Hermitian relation between transposed entries.

**Theorem 1.5 (First spectral moment).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_trace_re`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_trace_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real trace of the BKM output of a rank-one outer product is the sum of the reference eigenvalues weighted by the squared moduli of the vector's eigenbasis coordinates.

**Theorem 1.6 (Hermitian rank-one output).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rank-one outer product formed in the reference eigenbasis is Hermitian after conjugation, so its BKM output is Hermitian as well.

**Theorem 1.7 (Spectral variance and the trace-square deficit).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_trace_sq_sub_trace_sq_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_trace_sq_sub_trace_sq_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit vector, its squared coordinate moduli form probability weights. If T bounds all absolute log-ratios of the positive reference eigenvalues, the real trace of the squared BKM output minus the square of its real trace is at least twice the weighted eigenvalue variance divided by 12 + T². The estimate follows by summing the scalar logarithmic-mean bound over pairs of eigenvalues.

**Theorem 1.8 (Trace of the BKM integral).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_trace_eq_trace_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_trace_eq_trace_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex matrix input, the BKM output has the same complex trace as the product of the reference and the input. The diagonal logarithmic-mean multipliers in the reference eigenbasis are the eigenvalues themselves.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.fromEigenbasis`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omegaLinear`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_isHermitian`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_isHermitian`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_trace_re`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_rankOne_trace_sq_sub_trace_sq_ge`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.omega_trace_eq_trace_mul`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSpectralVariance.trace_conjStarAlgAut_symm`
- Dependency: [D5/S3/Quantum/Recovery/BKMRelativeDensity](BKMRelativeDensity.md)
