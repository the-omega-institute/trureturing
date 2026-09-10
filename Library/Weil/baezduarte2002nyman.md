---
bibkey: baezduarte2002nyman
authors: Luis Báez-Duarte
year: 2002
title: A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/math/0202141v2
claim: The Introduction defines the real-dilation fractional-part family in L2(0,infinity), its linear hull B, and the closure of B used in the Nyman-Beurling criterion.
strata_touched:
  - D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector
  - D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.fullRealClosure
license: citation-only
triage: anchor
---

# Real-dilation Beurling family and closure

The cited version is arXiv math/0202141v2, revised 18 February 2002, also
the date printed in the paper. Introduction, PDF p. 1 (TeX lines 55–75),
works in the half-line Hilbert space and defines

\[
\mathcal H=L_2(0,\infty),\qquad
\rho_a(x)=\operatorname{fract}\!\left(\frac{1}{ax}\right),
\quad a\in\mathbb R,\ a\geq1,
\qquad
\mathcal B=\operatorname{span}\{\rho_a:a\in\mathbb R,\ a\geq1\}.
\]

It then uses the norm closure of B in the stated Nyman-Beurling criterion,
RH if and only if chi belongs to that closure. This is the source of the
two displayed definitions cited here.

The repository makes the complexification explicit: realSourceVector is
the Lp class of the real-valued fractional part embedded by Complex.ofReal
in Lp(C,2,volume restricted to (0,infinity)); square integrability is proved
before forming that class. fullRealClosure takes the topological closure
of the complex span of all these vectors with real a at least one. Thus
"real" describes the dilation parameter, while the formal span uses complex
scalars. The citation attests the mathematical family and span/closure
construction, not a printed Lean quotient construction or a separate
formal scalar-identification theorem.

The Introduction prints chi for the indicator of (0,1], while the Abstract
and the repository use (0,1). These representatives differ at the endpoint
1; that singleton has zero Lebesgue measure, so this is an almost-everywhere
endpoint convention in the Lp quotient, not pointwise equality.

Theorem 1.1 on p. 1 (TeX lines 82–88) specifically asserts RH if and only
if chi belongs to the closure of the natural-dilation span Bnat. It does
not identify the natural and real closed subspaces; the discussion on
p. 2 distinguishes them. Neither that strengthening nor either RH
equivalence is proved by this provenance note. The local Mellin separator,
its norm, and the conditional E11 distance bounds remain repository-derived
results and are not attributed to Theorem 1.1.

## Verified locator

The pinned record is https://arxiv.org/abs/math/0202141v2, Introduction,
PDF p. 1, real-dilation family and B closure. The supplied official-source
intake identifies these bytes:

- [PDF](https://arxiv.org/pdf/math/0202141v2), SHA256
  `3ce4aff466443c71094affc1f8b6f5f0dd36cb4377dc5d2ceddbd2537c1d1819`.
- [Source archive](https://arxiv.org/src/math/0202141v2), SHA256
  `3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`;
  extracted TeX SHA256
  `382f48f180fefbfa735fb181859202275a7fcb22e332112fe7ab5ff8c57e13e2`.

This note paraphrases the cited definitions; no source text or license
grant is imported. The citation uses the pinned arXiv URL; no DOI is asserted.
