---
bibkey: shortuniformity2026robininterfaces
authors: trureturing research synthesis
year: 2026
title: Short-interval higher-order uniformity and the same-source Robin tail
doi: null
url: https://arxiv.org/abs/2610.09567v1
claim: "Versioned short-interval Gowers, nilsequence and well-factorable estimates retain distinct models, weight hypotheses and error rates; no interface from these statements to the complete same-source signed Robin tail is supplied."
strata_touched: []
license: citation-only
triage: anchor
---

# Short-interval uniformity: reusable inputs and the unpaid Robin interface

This note records the statements and parameter correspondence of three
versioned primary manuscripts. Their complete proofs are not independently
audited here. The published suppliers are cited directly; no new supplier
proof, signed Robin estimate, exhaustive literature survey or Lean
certification is claimed.

## Quantitative Gowers uniformity with its Siegel model

Joni Teräväinen, *Quantitative Gowers uniformity of the primes in intervals
of length $X^{5/8+\varepsilon}$*,
[arXiv:2610.03707v1](https://arxiv.org/html/2610.03707v1),
version 2 October 2026, §1, Theorem 1.1, equations (1.3)–(1.5).

For fixed integer $k\ge2$ and $\varepsilon>0$, set $a_k=2^{-k-2}$.
There is $c=c(k,\varepsilon)>0$ such that

$$
2\le X^{5/8+\varepsilon}\le H\le X,\qquad
2\le w\le\exp((\log X)^{1/10})
$$

implies, for the source's normalized interval Gowers norm,

$$
\|\Lambda-\widetilde\Lambda_w\|_{U^k(X,X+H]}
\ll_{k,\varepsilon}w^{-a_k}+\exp(-(\log X)^c).
$$

Here $P(w)=\prod_{p\le w}p$ and
$\Lambda_w(n)=P(w)\mathbf1_{(n,P(w))=1}/\varphi(P(w))$.
If there is a level-$w$ Siegel zero $\beta$ with its primitive real
character $\chi$, the model is
$\widetilde\Lambda_w(n)=\Lambda_w(n)(1-\chi(n)n^{\beta-1})$;
otherwise it is $\Lambda_w$. This model cannot silently be replaced
by the constant function or by the full CA layer measure.

## A shorter interval range with different quantitative conclusions

Kaisa Matomäki, Mayank Pandey, Javier Pliego, Joni Teräväinen and
Mengdi Wang, *Higher order uniformity of the primes and cancellation
of the Möbius function in shorter intervals*,
[arXiv:2610.09567v1](https://arxiv.org/html/2610.09567v1),
version 7 October 2026, §1.1, Theorems 1.1–1.2.

Theorem 1.1 gives, for fixed integer $s\ge1$ and $\varepsilon>0$,
uniformly on $X\ge3$ and $X^{3/5+\varepsilon}\le H\le X$,

$$
\|\Lambda-\Lambda_X^\sharp\|_{U^s(X,X+H]}=o_{s,\varepsilon}(1).
$$

Its Cramér model uses $R=\exp((\log X)^{1/10})$ and
$\mathcal P(R)=\prod_{p<R}p$; it has no explicit Siegel correction
in its definition. This qualitative statement does not inherit
Teräväinen's displayed quantitative rate merely by combining citations.

Theorem 1.2 separately gives arbitrary fixed logarithmic savings for
$\mu$ and for $\Lambda-\Lambda_X^\sharp$ against the specified polynomial
nilsequences. It requires
$X^{3/5+\varepsilon}\le H\le X^{1-\varepsilon}$, fixed degree and
dimension $d,D$, complexity and Lipschitz norm at most $1/\delta$,
and $0<\delta<1/2$. The bound is
$O_{L,\varepsilon,d,D}(\delta^{-O_{d,D}(1)}H/(\log X)^L)$ for every
fixed $L>0$. The starred norm also takes the supremum over arithmetic
progressions contained in the interval. An arbitrary arithmetic sign
selector has not been proved to belong to this testing class.

Theorem 1.4, §1.2, improves the untwisted Möbius interval threshold from
$11/20$ to $19/35$: uniformly for
$X^{19/35+\varepsilon}\le H\le X$ it gives

$$
\left|\sum_{X<n\le X+H}\mu(n)\right|
\ll_\varepsilon H/(\log X)^{1/3-\varepsilon}.
$$

This is a cited improvement in interval length, not a square-root bound
for the full Mertens prefix. The project's actual Fibonacci identity
$e=\mu*\beta$ and its nonvanishing multiplier are already established
in FIB §§384–385; here $\beta_d=\log(1-(-\varphi^{-2})^d)$ is a
coefficient sequence, distinct from the ATOM $\beta=\rho(\alpha)$.
Those bridges are reused; no new convolution or determinant proof is added.

## The actual persistence clock fits; the amplitude is still unpaid

The [existing same-source persistence input](../Arith/caveney2012sacaga.md#a-wider-actual-price-interval-for-the-same-supplied-power-excess)
uses $A=\log N$, a particular fixed supplied $0<\eta<1/2$, and

$$
h=\lambda A^{1-\eta/2}\exp((\log A)^{1/4}/2),\qquad \lambda>0.
$$

At the prime scale $X=A$, $H=h$, both Gowers interval ranges hold
eventually, for example with fixed $\varepsilon=1/16$. For the
nilsequence statement instead take
$\varepsilon=\min(1/16,\eta/4)$, so that its additional upper
bound $h\le A^{1-\varepsilon}$ holds eventually. The supplied source
conditions and exponent are unchanged. The uniformity in the starting
point permits an arithmetic choice of that point; it does not by itself
authorize an unrestricted testing weight.

Even at the largest permitted $w$, the first quantitative error allowance
contains $\exp(-a_k(\log A)^{1/10})$. Its ratio to the source excess
scale $A^{-\eta}$ tends to infinity. Likewise every fixed logarithmic
saving is weaker than that power scale, while the qualitative Gowers
conclusion gives no rate. These compare the stated error allowances;
they do not assert lower bounds for the actual errors. An additional
proved arithmetic gain could change the comparison.

The [actual full-state sampling interface](mantovanelli2026primeworkload.md)
retains all exponents, tied layers and the actual size $\log C_b$.
Neither a Gowers norm of a centered model difference nor a nilsequence
test identifies its complete post-event Robin sign. A testing interface,
quantitative gain and control of the common untruncated baseline all
remain necessary; length admissibility alone supplies none of them.

## Well-factorable distribution preserves the total-prime baseline

James Maynard, *Primes in arithmetic progressions to large moduli II:
Well-factorable estimates*,
[arXiv:2006.07088v1](https://arxiv.org/html/2006.07088v1),
version 12 June 2020, Definition 2 and Theorem 1.1, gives

$$
\sum_{\substack{q\le Q\\(a,q)=1}}\lambda_q
\left(\pi(x;q,a)-\frac{\pi(x)}{\varphi(q)}\right)
\ll_{a,L,\varepsilon}\frac{x}{(\log x)^L},
\qquad Q\le x^{3/5-\varepsilon}.
$$

The residue $a$ and $L,\varepsilon>0$ are fixed. The weights must be
triply well factorable: for every real factorization
$Q=Q_1Q_2Q_3$, $Q_i\ge1$, they admit a convolution of three
1-bounded sequences supported on $[1,Q_i]$. Full source conditioning
has not supplied such weights. The center is the actual $\pi(x)$;
the $q=1$ discrepancy is identically zero, so this theorem does not
bound the common total-prime error. For the Robin consumer the prime
scale is $x\asymp A$, not $N=e^A$. Replacing it by $N$ to turn a
logarithmic saving into $A^{-L}$ changes the actual summation problem.
