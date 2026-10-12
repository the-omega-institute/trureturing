---
bibkey: ramare2008bruntitchmarsh
authors: Oliver Ramaré and Jan Christoph Schlage-Puchta
year: 2008
title: Improving on the Brun-Titchmarsh Theorem
doi: null
url: https://arxiv.org/abs/2607.04283v1
claim: A uniform interval upper bound for actual primes pays the local first-layer inventory capacity used with the retained integer-competitor concavity cost.
strata_touched: []
license: citation-only
triage: anchor
---

# A uniform interval upper bound, directly reused

The primary is *Improving on the Brun-Titchmarsh Theorem*,
[arXiv:2607.04283v1](https://arxiv.org/pdf/2607.04283v1),
Theorem 1.1, PDF page 2 of 19. Its archive cover identifies the paper
as published in *Acta Arithmetica* **131**(4) (2008), 351--366.
The arXiv version was uploaded in July 2026; the sieve theorem is a
2008 result, not a new 2026 prime-distribution improvement.

The downloaded PDF has SHA-256
`bc3aab7b452a7598506e1c123724a6626cc9dc12c1b667c07a6e99faa211b5ef`.
These facts identify the inspected statement; the full sieve proof and
its computations were not independently reproduced or Lean-verified.

The theorem states that there is $N_0$ such that

$$
\pi(M+N)-\pi(M)\le\frac{2N}{\log N+3.53}
\qquad(N\ge N_0,\ M\ge1).
$$

Its uniformity in the starting point is essential. The project uses
outward integer rounding, so it requires no extension of the theorem
to a new class of real input parameters. The start $N_0$ is existential
in this statement; no numerical value is supplied here. There is no
RH assumption, signed prime-error conclusion, interval asymptotic or
almost-all exceptional-center selection in this input.

The [existing price-gap application](../Estimation/trureturing2026pricegapconvexity.md#the-prime-interval-supplier-and-both-competitor-costs-control-actual-stock)
uses it for first-layer activation primes in $(B-1,B+z)$ when
$z\ge\sqrt B$. After weighting each actual prime by its own $\log p$,
the uniform capacity coefficient may be any fixed $c>4$, with the
complete higher-layer contribution paid by an existing $O(\sqrt B)$
frontier bound. The subsequent $8/5+\eta$ coefficient comes from that
application's retained work-plus-concavity account; it is not a theorem
attributed to this paper.
