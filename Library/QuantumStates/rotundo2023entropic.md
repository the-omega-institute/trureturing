---
bibkey: rotundo2023entropic
authors: Antonio F. Rotundo; René Schwonnek
year: 2023
title: "An entropic uncertainty principle for mixed states"
doi: 10.1103/PhysRevResearch.6.033043
url: https://arxiv.org/abs/2303.11382v1
claim: "Conjecture 1 (Extended MUB regime): a doubly stochastic matrix has mixed operator norm d^(1-lambda-mu) whenever ((1-mu)/mu)((1-lambda)/lambda) >= sigma_2^2."
strata_touched:
  - D5/S3/Quantum/Information/ExtendedMubNormRefutation
license: citation-only
triage: anchor
---

# An entropic uncertainty principle for mixed states

Antonio F. Rotundo and René Schwonnek, arXiv:2303.11382v1;
Phys. Rev. Research 6, 033043 (2024).

Conjecture 1 on p. 2 of the arXiv v1 paper states:

> (Extended MUB regime). Let $C^{(2)}$ be a doubly stochastic matrix.
> Its norm is equal to that of $C^{(2)}_{\mathrm{MUB}}$, i.e. it is given
> by eq. (7), as long as
> $\frac{1-\mu}{\mu}\frac{1-\lambda}{\lambda}\ge\sigma_2^2$,
> where $\sigma_2$ is the second largest singular value of $C^{(2)}$.

Equation (7) is
$\log\|C^{(2)}_{\mathrm{MUB}}\|_{1/\mu\to1/(1-\lambda)}
=(1-\lambda-\mu)\log d$.
Equation (5) defines the operator norm using the usual vector p-norms,
with complex vectors. The formalized claim uses real vectors and real
doubly stochastic matrices, with $d\ge2$ and $0<\mu,\lambda<1$.
The real vector producing the strict lower bound is also an admissible
complex vector in equation (5).

The journal version restates Conjecture 1 as an entropic inequality.
The norm statement in arXiv v1 is the statement refuted by
`D5/S3/Quantum/Information/ExtendedMubNormRefutation.result`;
the journal's entropic reformulation is outside this theorem.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevResearch.6.033043
- URL: https://arxiv.org/abs/2303.11382v1 — p. 2, Conjecture 1 and
  equations (5), (7), (9).
