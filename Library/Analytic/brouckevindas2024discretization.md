---
bibkey: brouckevindas2024discretization
authors: Frederik Broucke; Jasson Vindas
year: 2024
title: A new generalized prime random approximation procedure and some of its applications
doi: 10.1007/s00209-024-03526-4
url: https://arxiv.org/abs/2102.08478v2
claim: Theorem 1.2 realizes any admissible continuous counting template by strictly increasing generalized primes with count discrepancy at most one and simultaneous exponential-sum control; it supplies no ordinary-prime or selected Robin-source sign estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Published generalized-prime realization supplier

The inspected primary is [arXiv:2102.08478v2](https://arxiv.org/abs/2102.08478v2),
revised 17 June 2024, [versioned PDF](https://arxiv.org/pdf/2102.08478v2)
and [HTML](https://arxiv.org/html/2102.08478v2).
The PDF has 15 pages and SHA-256
`66b727b7b5b151844558b88c1495e1eca902b1c0ea01840b5e783f4b2ff0c9c8`.
Theorem 1.2 and equation (1.3) were inspected on printed p.2;
the formula was also checked against the HTML mathematical text.
The arXiv record and Crossref identify the publication as
*Mathematische Zeitschrift* 307 (2024), Article 62,
[DOI 10.1007/s00209-024-03526-4](https://doi.org/10.1007/s00209-024-03526-4).
The publisher's full text and the complete source proof are not
independently audited here. No source text is vendored or Lean
verification claimed.

## Exact reusable statement

Theorem 1.2 assumes that $F:[1,\infty)\to\mathbb R$ is nondecreasing,
right-continuous, unbounded, $F(1)=0$, and
$F(x)\ll x/\log x$. It gives an unbounded nondecreasing sequence
$\mathcal P=(q_j)$ of real generalized primes, with $q_j>1$, such that

$$
|\pi_{\mathcal P}(x)-F(x)|\le2
\qquad(x\ge1),
$$

and, simultaneously for all real $t$ and all $x\ge1$,

$$
\left|\sum_{q_j\le x}q_j^{-it}
       -\int_1^x u^{-it}\,dF(u)\right|
\ll\sqrt x+
\sqrt{\frac{x\log(|t|+1)}{\log(x+1)}}.
\tag{BV1}
$$

If $F$ is continuous, the sequence may be chosen strictly increasing
with $|\pi_{\mathcal P}(x)-F(x)|\le1$, retaining (BV1).
The implicit constant in (BV1) belongs to the chosen template;
no uniform constant over every admissible $F$ is asserted.
The count bound at $t=0$ is the separate stronger conclusion,
not the weaker $O(\sqrt x)$ obtained by using (BV1) alone.

The source's introduction explicitly attributes the predecessor
random approximation method to Diamond–Montgomery–Vorhauer,
*Beurling primes with large oscillation*,
[DOI 10.1007/s00208-005-0638-2](https://doi.org/10.1007/s00208-005-0638-2),
and its refinement to Zhang. This attribution was read in the
Broucke–Vindas primary; those predecessor proofs are not
independently verified here. Reuse Theorem 1.2 for realization rather
than reproducing any of these discretization constructions.
