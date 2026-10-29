---
bibkey: acostababb2024partial
authors: Ryan L. Acosta Babb
year: 2024
title: A partial converse to the Riemann–Lebesgue lemma for Bessel–Fourier series of order zero
doi: 10.48550/arXiv.2410.17681
url: https://arxiv.org/abs/2410.17681v1
claim: "Conjecture 1 asserts nonnegativity of the explicit weighted order-zero Bessel kernel for 0 <= alpha <= 1/2, every natural mode count and every x in [0,1]."
strata_touched:
  - D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2410.17681

Source: https://arxiv.org/abs/2410.17681v1

Full text: https://arxiv.org/pdf/2410.17681v1

## Source assertion and definitions

Conjecture 1, p. 10, verbatim TeX:

```tex
For all, $0\leq\alpha\leq\frac{1}{2}$, $M\in\N$ and $x\in [0,1]$, $K^{\alpha}_M(x)\geq 0$.
```

The macro `\N` is `\mathbb{N}`. Lemma 2.2, p. 6, states:

```tex
Let $j_m$ denote the $m\th$ positive zero of $J_0$. Then
```

Section 3, p. 7, states:

```tex
Let us write $$S^{\alpha}_m(x) = \sum_{k=1}^{m}j_m^{\alpha}J_0(j_k x).$$
We will need the following `modified Fej\'er kernel' for the Bessel--Fourier series:
\[
    K^{\alpha}_M(x) := \frac{1}{M+1}\sum_{m=1}^{M}S^{\alpha}_m(x)
            = \sum_{m=1}^{M}\left(1-\frac{m}{M+1}\right)j_m^{\alpha}J_0(j_m x).
\] We will also set $K^{\alpha}_0(x) \equiv 1$ when $M=0$.
```

The printed S has a factor indexed by m inside the sum over k; it does
not imply the displayed Cesaro equality. The refutation concerns the
explicit weighted formula on the right and its separate value at M=0,
as specified in [#22175](https://github.com/the-omega-institute/trureturing/issues/22175).
The printed S is kept separately. The real owner `nbessel 0` is the
standard order-zero Bessel series. Positive zeros are indexed from one.
The recursive infimum sequence needs only its first two entries for this
counterexample; their attainment and rational enclosures are proved.

## Scope of the refutation

The repository refutes the assertion at alpha=1/2, M=2, x=999/1000.
It does not prove the proposed uniform alpha rectangle or sharp M=2
threshold, or decide positivity for other mode counts. The false
positivity premise removes the proposed conditional route to the source's
stronger coefficient construction; it does not refute those existence
conclusions or Conjecture 2.

The journal version, *On the rate of growth of Bessel–Fourier coefficients
for integrable functions*, J. Math. Anal. Appl. 559 (2026), 130440,
DOI 10.1016/j.jmaa.2026.130440, retains Conjecture 1 on p. 11.
The target is the unambiguous order-zero arXiv v1 statement above.

## Computation and literature boundary

The exact rational experiment is in
`the-omega-institute/trureturing-experiments`, commit
`b01beb85ba641ba44f5d5711499d06a46af0ddef`, at
`docs/reports/acosta-babb-bessel-kernel/check.py`, SHA-256
`ce3c873f27837df0248c09ec4c25d95d6a159658aeaed7ef0457db174a8acef1`.
The command `python3 docs/reports/acosta-babb-bessel-kernel/check.py`
has recorded exit code 0 and final output `ALL_CHECKS_OK` in #22175.
It checks rational inequalities for root signs, the point enclosure,
the endpoint-flux margin 27843/500000, curvature bound
895734319/60000000 and power comparisons for a proposed threshold
between 17/50 and 7/20. The uniform-family and threshold analytic
bridges are not Lean theorems of this delivery.

Literature completeness is ASSUMED-UNVERIFIED. The partial screen in
#22175 found no settlement in the texts successfully read. MathOverflow,
rate-limited citation queries, unread final journal texts, uncapped broader
arXiv results and full classical treatises remain outside that screen.
The refutation is repository-derived; no originality claim is made.
