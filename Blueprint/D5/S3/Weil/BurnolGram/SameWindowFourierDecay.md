# Fourier decay of the actual same-window error

## Abstract

The actual same-window cutoff error has an interior derivative budget and angular Fourier decay with both endpoint jumps paid.

Use the actual interior-box convolution cutoff chi and its actual bundled Weil test T=chi*p in the original window [-a,a]. Assume h>0, 4h<=a, a smooth even complex input p, and bounds |p|<=M, |p'|<=M1 with M,M1>=0 on that window. The zero-extension error is E=1_{(-a,a)}p-T; it may jump at both endpoints and is not asserted to be a Weil test function.

**Theorem 1.1 (Only the two boundary strips pay the derivative error).**

Lean statement: `D5/S3/Weil/BurnolGram/SameWindowFourierDecay.sameWindowSmoothTrial_derivative_L1_error_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/SameWindowFourierDecay.sameWindowSmoothTrial_derivative_L1_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of |(p-T)'| on the closed original window is at most 2M+4h*M1. The plateau makes the derivative vanish in the central open interval. Two strips of total length 4h pay the p' term, while the actual cutoff derivative has integral at most two. Integrability of that derivative follows from smoothness and compact support; the bound is not inferred from a totalized non-integrable integral.

**Theorem 1.2 (The actual angular transform pays both endpoint jumps).**

Lean statement: `D5/S3/Weil/BurnolGram/SameWindowFourierDecay.sameWindowSmoothTrial_fourier_error_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/SameWindowFourierDecay.sameWindowSmoothTrial_fourier_error_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem establishes Integrable E and, for every real angular frequency t, integrability of exp(-i*t*x)*E(x). Its Fourier integral has norm at most 4M*h for all t and at most (4M+4h*M1)/|t| when t is nonzero. The live interval integration-by-parts identity uses the smooth interior error p-T and retains the traces p(-a), p(a). Their combined norm costs 2M in addition to the proved interior derivative budget. Endpoint values of the open-window zero extension do not erase these traces, and evenness does not cancel them at a general real frequency. The kernel uses angular frequency with no extra 2*pi factor. This module supplies no weighted integral estimate, closed-form comparison, signed negative Weil trial, or RH conclusion.

## References

- Truth anchor: `D5/S3/Weil/BurnolGram/SameWindowFourierDecay.sameWindowSmoothTrial_derivative_L1_error_le`
- Truth anchor: `D5/S3/Weil/BurnolGram/SameWindowFourierDecay.sameWindowSmoothTrial_fourier_error_bounds`
- Dependency: [D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff](SameWindowSmoothCutoff.md)
