---
bibkey: cloitre2026fibonacciddp
authors: Benoit Cloitre
year: 2026
title: "Fibonacci, Dirichlet, and Gauss in a single sum"
doi: null
url: https://arxiv.org/abs/2607.20960v1
claim: The fractional-part sum of Fibonacci ratios has parity-dependent remainders governed by the Gauss circle and Dirichlet divisor error terms; this sharpens the unweighted Fibonacci gauge but does not estimate the weighted source used by the FIB Robin bridge.
strata_touched: []
license: citation-only
triage: anchor
---

# Fibonacci fractional parts and the two classical error problems

The source is [arXiv:2607.20960v1](https://arxiv.org/pdf/2607.20960v1), submitted 23 July 2026. This card records the main theorem interface from that version. It is a preprint; the proof and constants were not independently audited here, and no Lean verification is claimed.

For

$$
\mathcal F(n)=\sum_{k=1}^{n}\left\{\frac{F_n}{F_k}\right\},
$$

the paper proves, for every $\varepsilon>0$,

$$
\mathcal F(n)=\frac{\pi}{8}n
 +\frac14\left(\Delta_C(n)-\Delta_C(n/2)\right)+O(n^\varepsilon)
\quad(n\ge3\text{ odd}),
$$

and

$$
\mathcal F(n)=\frac{3\log 2}{4}n
 +2\Delta_H(n/2)-5\Delta_H(n/4)+2\Delta_H(n/8)+O(n^\varepsilon)
\quad(n\ge4\text{ even}),
$$

where $\Delta_C$ is the Gauss circle error term and $\Delta_H$ is the Dirichlet divisor error term. The paper also proves the converse exponent implications: an $O(n^{\theta+\varepsilon})$ remainder along the odd, respectively even, Fibonacci indices is equivalent to the corresponding classical error exponent. The generalized second-order recurrence theorem exchanges the parity profiles for the ordinary Lucas sequence.

This result refines the earlier $O(\sqrt n)$ Fibonacci fractional-part asymptotic recorded in [Cloitre's regular-arithmetic note](cloitre2026regulararithmetic.md). It is an Abelian sum over the Fibonacci index. It does not define the project's Zeckendorf five-window address, the affine family $1+F_rg$, or the complete point value $\sigma(1+F_rg)/(1+F_rg)$.

The project's current weighted interface uses

$$
A_n=\sum_{k=1}^{n}F_k\left\{\frac{F_n}{F_k}\right\}.
$$

The cited theorem has no $F_k$ weight, so it cannot be substituted into that estimate by changing the leading constant. A further weighted partial-summation or local-residue argument would be required, together with a proof that the resulting kernel transports the ordinary divisor coefficients needed for Robin. The paper therefore sharpens the analytic history of the Fibonacci gauge and identifies its exact classical error source, while leaving the FIB-to-Robin point-value bridge open.
