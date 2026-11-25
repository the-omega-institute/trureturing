# Dyadic decomposition of the strip energy

## Abstract

For faithful bipartite matrices, the partial-trace Umegaki loss splits into dyadic logistic boundary energies and an exact remainder.

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

**Definition 1.6 (Joint and retained log frequency).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.physicalFrequency`

*Formalization.* `D5/S3/Analytic/PetzDyadicStripEnergy.physicalFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a joint eigenvector pair of the source and reference and a retained eigenvector pair of their marginals, the frequency is the reference joint log eigenvalue minus the source joint log eigenvalue plus the source marginal log eigenvalue minus the reference marginal log eigenvalue. Faithfulness gives positive eigenvalues for both actual partial traces.

**Definition 1.7 (Physical spectral coefficient).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.physicalCoefficient`

*Formalization.* `D5/S3/Analytic/PetzDyadicStripEnergy.physicalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the joint source and reference eigenbasis entry of the source square root times the lifted source and reference marginal rank-one projections in that order. The environmental factor of each lift is the identity. The indexing keeps every eigenvector, including repeated eigenvalues.

**Theorem 1.8 (Partial-trace entropy loss as a spectral quadratic).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_eq_stripEnergy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_eq_stripEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any pair of faithful joint matrices on a finite retained space times a finite nonempty environment, subtract the Umegaki trace-log expression of their actual marginals from that of their joint matrices. This equals the sum over all joint eigenvector pairs of the strip quadratic on their physical frequencies and coefficients.

The source edge is the source square root times the two lifted projections. The reference edge is the product of the two lifted projections times the reference square root and the square root of the marginal eigenvalue ratio. Partial-trace adjunction reduces both Hilbert–Schmidt Gram matrices to the same diagonal. The joint frequency shift cancels from the kernel differences, so the logistic and hyperbolic cotangent terms cancel after the joint summation. The remaining linear frequency is the trace pairing with the joint and marginal logarithms.

**Theorem 1.9 (Exact finite decomposition and lower estimate for Umegaki loss).**

Lean statement: `D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_dyadic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural cutoff M and faithful joint pair as above, sum the logistic boundary energy over joint eigenvector pairs and over levels m less than M. Each level uses the physical frequencies divided by 2^m and the original coefficients, with weight 2^m. The sum is nonnegative and bounded above by the Umegaki loss. The difference is the sum of the physical strip quadratics at frequencies divided by 2^M, with weight 2^M.

## References

- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.logisticEnergy`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.physicalCoefficient`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.physicalFrequency`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.remainder_eq_two_mul_stripGram_half`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic_lower_bound`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_dyadic`
- Truth anchor: `D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_eq_stripEnergy`
- Dependency: [D5/S3/Analytic/PetzStripGramRemainder](PetzStripGramRemainder.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiKernelContraction](../Quantum/Divergence/UmegakiKernelContraction.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinementPetz](../Quantum/Recovery/BKMFlagRefinementPetz.md)
