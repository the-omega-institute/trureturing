---
bibkey: maynardpratt2023halfisolated
authors: James Maynard and Kyle Pratt
year: 2023
title: Half-isolated zeros and zero-density estimates
doi: null
url: https://arxiv.org/abs/2206.11729v2
claim: The half-isolated subset count and the flexible-detector proof supply original Robin subhead allowances under their distinct local isolation and clock conditions; neither bounds all zeros or the remaining signed head.
strata_touched: []
license: citation-only
triage: anchor
---

# Half-isolated zeros and zero-density estimates

The inspected source is [author version v2](https://arxiv.org/pdf/2206.11729v2),
29 May 2023. The locators below refer to that version. Reading the stated inputs
is not an independent audit of their complete proof.

Definitions 8--9, printed pp.6--7, call $\rho_0=\beta_0+i\gamma_0$
$Y$-half-isolated if every zero $\rho'=\beta'+i\gamma'$ within
$(\log|\gamma_0|)^2$ satisfies either
$|\beta'-\beta_0|\le1/(10\log Y)$ and $\gamma'\ge\gamma_0$, or
$\beta'\le\beta_0-(\log\log|\gamma_0|)^2/\log Y$.
It is half-isolated if such a $Y$ exists with
$(\log\log|\gamma_0|)^3\le\log Y\le\log|\gamma_0|/\log\log|\gamma_0|$.

Theorem 4 and Corollary 5, printed p.3, are unconditional. The former supplies
an existential short zero-detecting Dirichlet polynomial. The latter bounds the
number of half-isolated zeros with $\beta\ge\sigma$, $\gamma\in[T,2T]$ by
$T^{2(1-\sigma)+o(1)}$. At each fixed $\sigma>1/2$, this implies an
$O_{\sigma,\epsilon}(T^{2(1-\sigma)+\epsilon})$ count for every fixed $\epsilon>0$.
The customary local zero-count bound can absorb multiplicities into such a loss
if the subset count is read as counting distinct locations.

These statements do not require Hypothesis $\mathcal F$. That finite-vertical-line
hypothesis is required for Theorem 1's density conclusion for all zeros; it cannot
be inferred from a fixed zero-free strip or a real-part bookkeeping mesh.

Lemma 35, printed pp.21--22, states a flexible-length detector under Hypothesis
$\mathcal F$. Its proof first uses that hypothesis to obtain $Y$-half-isolation
at every required scale, then applies Proposition 16 recursively. The detector
family size, coefficient bounds and lower detection threshold have fixed powers
of $\log\log T$ in their exponents; the support is within corresponding factors
of the chosen target length. The [all-scale local application](../Estimation/trureturing2026pricegapconvexity.md#an-all-scale-half-isolated-sector-is-paid-also-at-supremum-one)
explicitly imposes that local property on its selected actual zeros and checks
this use of the published proof. Its quantitative count is derived in that
consumer; it is not attributed to Corollary 5 for the whole half-isolated class.

The [original Robin source application](../Estimation/trureturing2026pricegapconvexity.md#half-isolated-zeros-pay-an-additional-part-of-the-original-compensated-head)
uses the subset count at finitely many fixed real parts, the complete original
$1/\gamma$ coefficient bound and the existing polynomial clock ceiling for fixed
$\Theta<1$. It retains the non-half-isolated complement. Corollary 5 alone supplies no error uniform at $\Theta=1$. All unselected zeros remain in the complementary head, including ordinary
half-isolated zeros that fail the stronger all-scale condition. Neither application
supplies a signed Li head bound, all-integer Robin or RH. No new density theorem or literature-priority claim is made.


## One local isolation scale and an explicit loss

The [single-scale Robin application](../Estimation/trureturing2026pricegapconvexity.md#one-local-isolation-scale-suffices-under-the-sharper-original-clock-ceiling)
uses Proposition 16 at one allowed $Y$ with $\log Y$ comparable to
$\sqrt{(\log T)(\log\log T)}$. Integer powers of the existing detector, with their
lower support, coefficient and detection losses retained, give the consumer's
quantitative subset count
$T^{2(1-\sigma)}\exp(C\sqrt{(\log T)(\log\log T)})$ on its stated compact
real-part interval. The source's stronger VC2 clock ceiling pays that loss also
at $\Theta=1$. This reuses the single-scale detector and classical mean square;
it does not require Lemma 35's all-scale premise or Hypothesis $\mathcal F$.
The count is derived in the consumer, rather than attributed to Corollary 5 for
the whole half-isolated class. All zeros failing the specified witness condition
remain in the complement, and neither the complete signed Robin bound nor RH
is supplied.


## The original source height also pays the ordinary high-frequency class

The [source-relative application](../Estimation/trureturing2026pricegapconvexity.md#the-ordinary-half-isolated-subhead-has-a-source-relative-allowance-at-supremum-one)
uses Corollary 5 through the existing SIH3 reciprocal-height bound for
all ordinary half-isolated zeros in the stated real-part and frequency
mask. It retains the small power of the actual core before comparing
it with the original unabridged positive height. This gives a vanishing
relative allowance and preserves the same remaining-head lower margin
also at $\Theta=1$, without a special witness scale or clock ceiling.
It does not upgrade the count, assert an absolute $o(M_XL_X)$ allowance
there, or control the complementary signed head. The argument uses the
original source's joint lower account in addition to the published
subset count; it is not attributed to Corollary 5 alone. No new density
theorem, all-integer Robin, RH or Lean certification is supplied.
