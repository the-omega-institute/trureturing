---
bibkey: martinez2024mirrorgamblersruin
authors: L. Martinez
year: 2024
title: "A symbolic computational approach to the generalized gambler's ruin problem in one and two dimensions"
doi: 10.48550/arXiv.2412.07667
url: https://arxiv.org/abs/2412.07667v1
claim: "Conjecture 5.1 gives a radical expression for the infinite-interval limit of the probability of reaching N from 1 when the left and mirror step probabilities are (1-p)/2 and the right step probability is p."
strata_touched:
  - D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2412.07667

Source: https://arxiv.org/abs/2412.07667v1

Conjecture 5.1 is on page 16; the first-step recurrence is in Section 4.1,
equation (15), page 11. Version 1 is the source of the quotations below.

# Mirror-step gambler's ruin

Section 4.1, page 11:

> Define $f(x)=f_N^{(p)}(x)$ as the probability that a particle starting at $x$ will eventually reach $N$.

Conjecture 5.1, page 16:

> Consider the generalization of the gambler’s ruin problem when we add a mirror step. If the particle starts at $x=1$, then
> $$\lim_{N\to\infty} f_N^{(p)}(1)=\frac{\sqrt{(p+1)(1-3p+4p^2)}-(1-2p)(p+1)}{2p(p+1)}$$
> whenever we restrict the particle moves by either moving from $x$ to $x-1$ with probability $q_1$, or from $x$ to $x+1$ with probability $p$, or from $x$ to $N-x$ with probability $q_2$ where $q_1=q_2=\frac{1-p}{2}$.

Here $0<p<1$. Conjecture 5.1 assigns $p$ to the right step, whereas the
symmetric recurrence in Section 4 assigns $p$ to the mirror step. The Lean
predicate `IsWinProbability` uses the probabilities in Conjecture 5.1.
The family is quantified over all solutions of the boundary recurrence for
$N\ge2$. Coincident destinations contribute their transition weights additively.

The finite solution for positive left, right and mirror weights $a,b,c$ with
$a+b+c=1$ is derived in the accompanying module. The proof uses the contracting
root of a reciprocal quadratic, verifies both boundary values and the recurrence,
and proves uniqueness by descent of an attained maximum to boundary zero.

The supporting experiment is
`the-omega-institute/trureturing-experiments`,
`docs/reports/martinez-2024-mirror-gamblers-ruin-limit/`, commit
`29616f484f91cf715c06c0b73367686d5013270c`.
Its `check.py` has SHA-256
`258eacb03afaded6b7ba029c4e3946fae07ebd4c0886ca7d1d38ab790dbaaecb`;
`python3 check.py` returns exit 0 (`RESULT PASS`). The numerical experiment
is independent support; the proof uses no experimental assumption.

The literature census recorded in issue #19080 found no settlement in the
source, the author's later papers, OpenAlex or Crossref. Completeness beyond
those searches is `ASSUMED-UNVERIFIED`; Semantic Scholar was rate-limited.
