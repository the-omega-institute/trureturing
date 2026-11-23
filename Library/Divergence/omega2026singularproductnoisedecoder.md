---
bibkey: omega2026singularproductnoisedecoder
authors: The Omega Institute
year: 2026
title: Singular product reference recovery through a finite memory
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/33561
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
`product-reference-stability/proof.txt` §4, gives the quadratic preparation correction and the
three-term bound for the joint residual. [PR #33561](https://github.com/the-omega-institute/trureturing/pull/33561)
contains the faithful-reference theorem.

## Formalization scope

For the kernel projection Q, the correction Q − (rank Q)τ leaves the trace unchanged and gives
the lower block a floor of Cη². The support block and the operator norm of the off-diagonal
block suffice to bound its Schur complement by the floor. The decoder uses the same encoder
and memory at every noise weight η². The resulting estimate controls the joint residual for
every finite reference density and joint probe through the same decoder.
