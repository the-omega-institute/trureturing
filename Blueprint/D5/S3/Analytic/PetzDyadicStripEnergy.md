# Dyadic decomposition of the strip energy

## Abstract

Halving the frequencies identifies the exact remainder after removing the logistic boundary energy.

**Theorem 1.1 (Strip Gram at half frequency).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.remainder_eq_two_mul_stripGram_half`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicStripEnergy.remainder_eq_two_mul_stripGram_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The remainder after subtracting the logistic Gram of the boundary jump equals twice the exact strip Gram entry at half of each frequency. The identity holds for every pair of real frequencies, including coincident and zero frequencies.

This is identity (2) of the project derivation Exact dyadic deficit decomposition for an actual mixed retained state. For a nonzero frequency difference, the hyperbolic double-angle identities give the relations between the logistic and coth factors at the two scales. At frequency difference zero both factors take the value one. The exponential addition law then matches the jump coefficients at either scale.

**Definition 1.2 (Exact strip quadratic energy).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy`

*Formalization.* `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real part of the finite quadratic form with the closed strip Gram as its kernel and complex coefficients paired by conjugation in the first argument.

**Definition 1.3 (Logistic boundary energy).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.logisticEnergy`

*Formalization.* `D5/S3/Analytic/PetzDyadicStripEnergy.logisticEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply each complex coefficient at frequency x by 1 minus exp(x/2). Integrate the squared norm of the resulting Fourier sum against pi/(cosh(2 pi t) + 1) on the real line.

**Theorem 1.4 (Exact finite dyadic decomposition).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite real frequencies and complex coefficients, and every natural cutoff M, the strip energy equals the sum over scales m from zero up to M of the logistic energies at frequencies divided by 2^m, each weighted by 2^m. The sum excludes scale M. Add 2^M times the strip energy at frequencies divided by 2^M.

The logistic Fourier transform identifies each integral with the quadratic form of the boundary jump. Applying the half-frequency identity inside the quadratic form gives the induction step while keeping the coefficient family fixed.

**Theorem 1.5 (Finite dyadic lower bounds).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every natural cutoff the sum of the weighted logistic energies is nonnegative and lies below the original strip energy, for the same arbitrary finite families.

The logistic integrals have nonnegative integrands. Apply positivity of the closed remainder to the doubled frequency family to obtain positivity of the strip energy at any scale.

## References

- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.logisticEnergy`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.remainder_eq_two_mul_stripGram_half`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic_lower_bound`
- Dependency: [D5/S3/Analytic/PetzStripGramRemainder](PetzStripGramRemainder.md)
