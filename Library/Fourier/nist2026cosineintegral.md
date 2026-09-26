---
bibkey: nist2026cosineintegral
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: Exponential, Logarithmic, Sine, and Cosine Integrals — Definitions and Interrelations
doi: null
url: https://dlmf.nist.gov/6.2.E11
claim: For positive real x the cosine integral is the negative improper integral of cos(t)/t from x to infinity; integration by parts gives the absolutely convergent sine-tail representation used here.
strata_touched:
  - D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier
license: citation-only
triage: anchor
---

# The real cosine integral

Equation (6.2.11) gives the negative improper cosine tail. Integration by parts
on a finite positive interval, followed by the vanishing of sin(R)/R, gives
Ci(x) = sin(x)/x - integral over t>x of sin(t)/t^2. The latter integral is
absolutely convergent for x>0 and is the existing Lean definition.

The Fourier multiplier is derived from this definition using finite frequency
bands and L2 convergence. This citation supports the classical Ci convention;
it is not claimed to provide a Lean proof or to state the exact L2 theorem.
No originality is claimed. Only bibliographic metadata and a mathematical
paraphrase are retained; no third-party implementation is copied.

## Verified locator

- URL: https://dlmf.nist.gov/6.2.E11

The equation was retrieved directly on 2026-09-26. DLMF uses other Fourier
normalizations in Chapter 1; the theorem instead uses Mathlib's phase
exp(-2 pi i x xi), verified in the pinned FourierTransform source.
