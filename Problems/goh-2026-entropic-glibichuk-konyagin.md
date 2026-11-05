---
slug: goh-2026-entropic-glibichuk-konyagin
bibkey: goh2026entropicenergy
doi: 10.2140/ent.2026.5.243
triage: theorem
motivation_gids:
  - D5/S3/Entropy/GohGlibichukKonyagin/Result.result
url: https://arxiv.org/abs/2406.18798v4
---

# Refutation of the unconditional entropic Glibichuk–Konyagin conjecture

## Problem

M. K. Goh, *On an entropic analogue of additive energy*, Essential Number
Theory 5 (2026), no. 2, 243–269, DOI 10.2140/ent.2026.5.243,
arXiv:2406.18798v4, §6, Conjecture 15, equation (89):

> **Conjecture 15 (Entropic Glibichuk–Konyagin lemma).** There is an integer $k\geq 3$ such that the following holds. Let $X$ be a random variable taking values in $\mathbf F_p$ for a prime $p$. Then for independent copies $X_1,\ldots,X_k,X'_1,\ldots,X'_k$ of $X$, we have
> $$H\{X_1X'_1+\cdots+X_kX'_k\} \geq \min(2H\{X\},\log p)-1. \qquad (89)$$

> In the original additive-combinatorial version of this statement, $k$ can be taken to be $3$, but any fixed integer is enough for our purposes.

The paper uses binary logarithms and discrete random variables.
No additional hypothesis on the law of X is stated.

### Formal reading

All local Lean names have prefix
`D5.S3.Entropy.GohGlibichukKonyagin.Result`.
Here $p$ is prime, $\mathbf F_p$ is `ZMod p`, $\delta_0$ is the point mass at zero,
and $U_p$ assigns mass $1/p$ to each field element. Outside the source quotation,
$H$ denotes Shannon entropy in nats and $H_{\mathrm{bits}}=H/\log 2$;
`shannonEntropy` is reused from `D5.S3.Entropy.MaxEntropy`.

A law $\mu:\mathbf F_p\to\mathbb R$ satisfies
$\mu(a)\ge0$ and $\sum_a\mu(a)=1$.
`sumLaw k μ` is the pushforward of the product weights
$\prod_{i\in\operatorname{Fin}k}\mu(x_i)\mu(x'_i)$,
indexed by $(x,x'):(\operatorname{Fin}k\to\mathbf F_p)^2$,
under $(x,x')\mapsto\sum_i x_i x'_i$.
Here $\operatorname{Fin}k=\{0,\ldots,k-1\}$.
For the convolution computation, `iter_product` uses tuples of pairs
$v:\operatorname{Fin}k\to\mathbf F_p\times\mathbf F_p$.
The standard equivalence `Equiv.arrowProdEquivProdArrow` sends
$v$ to its two projection functions; its inverse sends $(x,x')$ to
$i\mapsto(x_i,x'_i)$. In `sum_spike`, `Equiv.sum_comp` proves
that this change of indexing preserves the entire pushforward sum.
Thus $Z=\sum_iX_iX'_i$ has exactly this law for the $2k$ independent copies.
`claim` retains the existential $k\ge3$, all primes $p$, all such laws,
and the constant $1$ in bits. `result` states exactly `¬ claim`.

## Motivation

The settling declaration is `D5/S3/Entropy/GohGlibichukKonyagin/Result.result`.
The source note is `D5/L/Entropy/goh2026entropicenergy`.
A large zero atom can suppress products without suppressing the
entropy contributed by a small uniform component.

## Gap

For each $k\ge3$ and every prime $p>2^{2k}$, the law
$\mu=(1-1/k)\delta_0+(1/k)U_p$ violates (89). There are infinitely many
primes above each fixed threshold. The refutation is a uniform family,
not a finite enumeration of fields.

## Route

Put $t=1/k$, $s=t^2(p-1)/p$ and $r=1-(1-s)^k$.
The product law is $(1-s)\delta_0+sU_p$. Convolving two laws of this
form sends their weights $t,u$ to $t+u-tu$, because the uniform law
is unchanged by translation. Induction gives the sum law
$(1-r)\delta_0+rU_p$. Bernoulli's inequality gives
$0\le r\le ks<1/k$.

The finite mixture entropy bracket, applied to $\delta_0$ and $U_p$, yields

$$t\log p\le H(\mu),\qquad H(Z)\le\log 2+r\log p.$$

Write $L=\log_2 p$. Since $k\ge3$, $2L/k\le L$. Therefore

$$\min(2H_{\rm bits}(\mu),L)-1-H_{\rm bits}(Z)
\ge L/k-2>0,$$

where the last strict inequality follows from $p>2^{2k}$.

## Falsifier

An error in the pushforward/product-law identity, the exact product
or convolution formulas, either entropy bound, or the change of
logarithm base would invalidate the refutation. The conjecture
places no condition excluding the zero-atom family.

## Evidence

**PROVED.** `D5.S3.Entropy.GohGlibichukKonyagin.Result.violation`
gives strict failure for every $k\ge3$ and every prime $p>2^{2k}$.
`D5.S3.Entropy.GohGlibichukKonyagin.Result.result` states `¬ claim`.
The private laws and entropy bounds are used in these proofs.

**COMPUTED.** The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d1d5f5c0ce89767ad3073f2a68e142082c750c03/experiments/goh-entropic-glibichuk-konyagin)
contains `goh-c15.py`, SHA-256
`f049c6b924b667fa737b25bb92000f0b92c2b35567e948ba13ad704bdf0fc506`.
Command: `python3 goh-c15.py`; exit code 0.
The exact tested scope is
$(k,p)\in\{(3,67),(3,257),(4,257),(5,1031)\}$.
The laws are exact rational vectors; the bit entropies and margins
use floating-point logarithms. The margins
$\min(2H_{\mathrm{bits}}(X),\log_2 p)-1-H_{\mathrm{bits}}(Z)$, rounded to three decimal places,
are respectively 2.179, 2.907, 2.026 and 1.909.
These computations illustrate the family and do not replace its proof.

The supplied literature search checked the published source version,
Gavalakis–Goh–Kontoyiannis arXiv:2604.20233v3,
Li–Gavalakis–Kontoyiannis arXiv:2506.20813v2,
Li arXiv:2607.29042v1, the Erdős problem 52 page and discussion,
conjectures.io and OEIS. No settlement of Conjecture 15 was found in
that supplied scope. Example 8.1 of arXiv:2506.20813v2 uses a zero-atom
mixture for a different entropy sum-product bound; the method itself
has that prior precedent.

## Triage

### What the settlement shows

- **PROVED.** Every proposed fixed $k\ge3$ fails, by `violation` and
  `result`. The entropy mechanism is quantified in the private
  `mul_spike`, `sum_spike`, `weight_bounds` and `spike_entropy`:
  most products vanish, while $H(X)$ remains at least $(\log p)/k$.
- **COMPUTED.** The four margins and their exact tested scope are
  listed in Evidence. The entropy values are numerical approximations.
- **PROVED (in prose).** The family is not uniform on any set.
  For $0<t<1$ and prime $p$, every nonzero point has mass $t/p>0$,
  while zero has mass $1-t+t/p>t/p$. Thus the support is the whole
  field and its masses are unequal. This applies to $t=1/k$, $k\ge3$.
- **OPEN.** The entropic assertion with $X$ uniform on a set, as in
  the original additive-combinatorial Glibichuk–Konyagin lemma,
  is not settled by this refutation.
- **PROVED (in prose).** For fixed $k$, a maximum-mass bound
  $\max_a\mu(a)\le c\le1-1/k$ excludes this family:
  its zero mass is $1-1/k+1/(kp)>1-1/k$.
  In particular, the bound $\max_a\mu(a)\le1/2$ excludes every
  member with $k\ge3$, since $1-1/k\ge2/3>1/2$.
- **OPEN.** Whether a proposed upper bound on max-probability
  suffices for an entropic sum-product theorem is not proved here.
- **PROVED.** Conjecture 15 cannot supply the paper's route to Conjecture 14:
  `result` refutes Conjecture 15, so that proposed derivation is unavailable.
- **OPEN.** Conjecture 14 itself is not refuted by this result.

## ASSUMED-UNVERIFIED

The literature search is the supplied bounded search; no new network
search is asserted. Google Scholar returned 403 and Semantic Scholar
429 in that search. Exhaustive literature coverage and priority are
unverified. The computational margins use finite-precision logarithms.
No strengthened uniform-set or max-probability conjecture, and no
settlement of Conjecture 14, is claimed.
