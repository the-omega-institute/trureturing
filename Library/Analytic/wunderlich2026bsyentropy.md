---
bibkey: wunderlich2026bsyentropy
authors: Henning Wunderlich
year: 2026
title: Finite-radius Jensen and relative-entropy formulations of the Balazard--Saias--Yor criterion
doi: null
url: https://arxiv.org/abs/2610.10584v1
claim: The preprint gives finite-radius Jensen identities and a relative-entropy saturation form of the established Balazard--Saias--Yor criterion; it supplies no Robin divisor-sum estimate or FIB source bridge.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite-radius Jensen and relative-entropy formulations of the Balazard--Saias--Yor criterion

The source is [arXiv:2610.10584v1](https://arxiv.org/pdf/2610.10584v1), submitted 6 October 2026. The paper is a preprint; its cited Jensen--Hardy boundary identities were not independently audited here, and no Lean verification is claimed.

## What is explicit

For $u(s)=(s-1)\zeta(s)$, the paper maps the unit disk to the left half-plane and applies Jensen's formula at finite radius. In the normalization centered at $s=-1/2$, the mapped trivial zeros contribute a telescoping product. The residual is a nonnegative sum or integral over mapped nontrivial zeros off the critical line. The paper also gives a one-parameter gamma-quotient version.

The later construction starts from the established Balazard--Saias--Yor boundary family. If $Z=|\Xi(T)/\Xi(0)|^2$, with law $\mu$ and size-biased law $\nu(dz)=z\mu(dz)/M$, Theorem 8.2 states

$$
D-D_{\rm KL}(\mu\|\nu)=4G\ge0,
$$

where $G$ is the positive off-critical zero correction in that normalization, and RH is equivalent to equality with the displayed constant $D$. The paper stresses that the data-processing equality is unconditional; the RH content is saturation of the external bound, not equality in data processing.

## Boundary for the Robin/FIB route

This criterion controls a zero-side logarithmic integral. It does not identify that integral with

$$
e^\gamma n\log\log n-\sigma(n)
$$

at the same integer, nor does it provide a signed estimate for the project's $\Phi$ or Möbius tail. A FIB address supplies an additive Zeckendorf source and does not determine the law of $|\Xi(T)|^2$ or the required boundary test function. Replacing the missing Robin estimate by the nonnegative Jensen defect would change the target.

The reusable research question is therefore an unproved interface: construct a common, source-preserving transform whose arithmetic projection is the Robin pointwise defect and whose analytic projection is this zero-side defect, with all endpoint and truncation errors retained. No such bridge is supplied by this preprint, so it is not a Robin or RH proof.
