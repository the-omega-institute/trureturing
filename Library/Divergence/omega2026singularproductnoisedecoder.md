---
bibkey: omega2026singularproductnoisedecoder
authors: The Omega Institute
year: 2026
title: Singular product reference recovery through a finite memory
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: A trace-zero quadratic correction to a replacement state realizes a kernel-admissible decoder direction with a uniform finite-noise error estimate.
strata_touched:
  - D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder
license: citation-only
triage: anchor
---

# Singular product reference recovery through a finite memory

## Verified locator

The internal manuscript *Exact first-order reconstruction under dominant product noise*,
`thermal-operation-width-renewal/fibonacci-observation-entropy/high-noise-product-reference-limit.txt`,
gives the singular-reference replacement construction in the converse. The companion
*Sharp stability of singular product fixed points through a finite memory*,
`product-reference-stability/proof.txt` §4, gives a quadratic isotropic regularizer and the
three-term bound for the joint residual. The formalization is in the
[trureturing repository](https://github.com/the-omega-institute/trureturing).

The faithful-reference theorem appears in [PR #33561](https://github.com/the-omega-institute/trureturing/pull/33561).

## Formalization scope

The formalization adapts the isotropic regularizer I/d − τ by adding mass on the kernel.
Writing ΠQ for the kernel projection, it uses Z = ΠQ − (rank ΠQ)τ. The subtraction compensates
for the added trace on the support. In σ = τ − ηK + Cη²Z, the kernel block has a floor of
Cη², which dominates the Schur term from the off-diagonal block. The decoder mixes the
replacement by σ with weight η, so the quadratic preparation correction contributes
−Cη³Z to the exact marginal displacement. The encoder and finite memory are reused at
every noise weight η². The resulting estimate controls the joint residual for every
finite reference density and joint probe through the same decoder.
