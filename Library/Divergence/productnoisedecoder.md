---
bibkey: productnoisedecoder
authors: The Omega Institute
year: 2026
title: Exact first-order reconstruction under dominant product noise
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: A decoder mixed with a replacement channel realizes any traceless Hermitian marginal direction at a faithful fixed point and gives an exact joint error identity.
strata_touched:
  - D5/S3/Quantum/Recovery/LocalCompression/ProductNoiseDecoder
license: citation-only
triage: anchor
---

# Faithful product-noise decoder perturbation

## Verified locator

The companion manuscript *Exact first-order reconstruction under dominant product noise*, in
`high-noise-product-reference-limit.txt`, supplies the faithful replacement construction in the
converse and the exact joint error expansion in the upper-bound proof of “A two-sided quantitative
bound when τ has a positive spectral floor.” The manuscript is an internal source. The
[repository](https://github.com/the-omega-institute/trureturing) contains the corresponding Lean module.

## Formalization scope

For the fixed encoder and decoder of the manuscript, a positive spectral floor of τ permits
the replacement density τ − K/L for every traceless Hermitian K and suitable L > 0. The
formalization keeps L and K explicit in the finite joint estimate. Postcomposing the decoder
with a mixture of the identity and the replacer gives the displayed decoder mixture by trace
preservation. The estimate applies to arbitrary finite reference densities and joint source densities.

Kato's Section VII gives the approximate local compression setting.
[Exact and Local Compression of Quantum Bipartite States](https://arxiv.org/abs/2309.07434v2)
