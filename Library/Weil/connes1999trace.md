---
bibkey: connes1999trace
authors: Alain Connes
year: 1999
title: Trace formula in noncommutative geometry and the zeros of the Riemann zeta function
doi: 10.1007/s000290050042
url: https://arxiv.org/abs/math/9811068v1
claim: The semilocal arithmetic trace formula has a rapidly decreasing remainder for each fixed finite place set and fixed compact Schwartz test. The estimate supplies neither a favorable signed renormalized-trace comparison nor uniform constants for growing support and place sets.
strata_touched: []
license: citation-only
triage: anchor
---

# Semilocal trace remainder and the remaining sign comparison

The primary text inspected is [arXiv:math/9811068v1](https://arxiv.org/pdf/math/9811068v1), 10 November 1998, associated with *Selecta Mathematica* 5 (1999), 29–106, DOI [10.1007/s000290050042](https://doi.org/10.1007/s000290050042). Its 88-page PDF SHA-256 is `dfd4e9924d8980f82e3da11fdea861d318fda8f5c7ba57ee659baf8631975053`. The locators below refer to this manuscript, without asserting byte equality with the publisher edition. Section VII's setup, Theorem 4, equations (33)–(35), Lemma 2 and its final estimate were checked in the primary text. This is source reuse, not independent verification of the entire trace-formula proof or a Lean implementation.

## The fixed-test source theorem

Let $k$ be a global field and $S$ a finite set of places containing the infinite places. Section VII uses

$$
A_S=\prod_{v\in S}k_v,\qquad
J_S=\prod_{v\in S}k_v^\times,\qquad
C_S=J_S/O_S^\times,
$$

with the source's basic character and Haar normalizations. The cutoff projections are $P_\Lambda$ and $\widehat P_\Lambda=\mathcal F P_\Lambda\mathcal F^{-1}$, and $R_\Lambda=\widehat P_\Lambda P_\Lambda$.

For a fixed compactly supported $h\in\mathcal S(C_S)$, Theorem 4, manuscript p.31, states

$$
\operatorname{Tr}(R_\Lambda U(h))=
2h(1)\log'\Lambda+
\sum_{v\in S}\int_{k_v^\times}'
\frac{h(u^{-1})}{|1-u|}\,d^*u+o(1)
\qquad(\Lambda\to\infty).
$$

The principal-value normalization is part of the theorem. Here $2\log'\Lambda$ is the source's integral of multiplicative Haar measure over $\{\Lambda^{-1}\le|a|\le\Lambda\}$ in $C_S$. It must not silently be replaced by a differently normalized logarithm.

Lemma 2, manuscript pp.35–37, strengthens the remainder in the proof. Its error terms are

$$
\delta_q(\Lambda)=\int\widehat g_q(u)
\bigl(\log|u|-2\log'\Lambda\bigr)_+\,du,
\qquad q\in O_S^\times,
$$

where the $g_q$ arise from a fixed smooth compact lift of $h$. The series of absolute values converges geometrically on the finitely generated $S$-unit group and satisfies

$$
\sum_{q\in O_S^\times}|\delta_q(\Lambda)|
=O_{S,h,M}(\Lambda^{-M})
\qquad\text{for every }M>0.
$$

This is a reusable arithmetic trace remainder. The quantifiers fix $S$, the character and $h$ before taking the cutoff limit. No explicit uniform constants for a changing place set or full changing unit-test family are supplied here.

## Common-test and cutoff obligations

The project's additive support parameter is $L$, its multiplicative support is $[\lambda^{-1},\lambda]$ with $\lambda=e^L$, and its prime-power cutoff is $c=e^{2L}$. Its common autocorrelation has multiplicative support in $[c^{-1},c]$. Relating it to the semilocal test requires the source's scaling-representation normalization: the unnormalized action and its unitary normalization carry different half-density factors. The [existing common-test account](frankliebseiringer2006hardy.md) retains the actual pole, prime-power and Gamma terms; this note does not replace it by a newly assumed trace identification.

The source's auxiliary trace cutoff $\Lambda$ is distinct from the support parameter $\lambda$. A FIB support schedule does not determine how the fixed-test error constants behave when $S$ or $h$ changes. The rapid remainder cannot simply be assigned to a growing actual-Weil finite-section error.

More directly, the theorem does not supply the favorable sign needed for the complete renormalized comparison. The expression uses a product of cutoff projections and subtracts $2h(1)\log'\Lambda$. A nonnegative unrenormalized trace, even if separately established for a chosen test, does not by itself bound the remainder after that subtraction. The source's full global discussion retains an RH-strength trace-formula obligation; the fixed finite-$S$ theorem does not discharge it.

Uniformity in every parameter is not logically necessary for every conceivable positivity argument: a valid signed approximation for each fixed test could suffice by taking its pointwise limit. Such a signed comparison has not been obtained here. That is a distinct obligation from the remainder's rate.

The [spectral construction](connesconsanimoscovici2026spectral.md) and [effective prolate bounds](karnikrombergdavenport2021prolate.md) offer other reusable inputs with different operator contracts. None of these notes establishes the missing common-function arithmetic sign or cofinal Weil positivity. RH remains unproved.
