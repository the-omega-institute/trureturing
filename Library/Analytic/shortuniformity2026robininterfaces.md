---
bibkey: shortuniformity2026robininterfaces
authors: trureturing research synthesis
year: 2026
title: Short-interval higher-order uniformity and the same-source Robin tail
doi: null
url: https://arxiv.org/abs/2610.09567v1
claim: "Versioned pointwise, mean-square, weighted, Gowers, nilsequence and well-factorable short-interval estimates retain distinct models, weight hypotheses and error rates; no interface from these statements to the complete same-source signed Robin tail is supplied."
strata_touched: []
license: citation-only
triage: anchor
---

# Short-interval uniformity: reusable inputs and the unpaid Robin interface

This note records the statements and parameter correspondence of
versioned primary sources. Their complete proofs are not independently
audited here. The published suppliers are cited directly; no new supplier
proof, signed Robin estimate, exhaustive literature survey or Lean
certification is claimed.

## Quantitative Gowers uniformity with its Siegel model

Joni Teräväinen, *Quantitative Gowers uniformity of the primes in intervals
of length $X^{5/8+\varepsilon}$*,
[arXiv:2610.03707v2](https://arxiv.org/html/2610.03707v2),
version 22 October 2026, §1, Theorem 1.1, equations (1.3)–(1.5).

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

## A stronger error on longer Möbius intervals

Matomäki–Teräväinen, *On the Möbius function in all short intervals*,
[arXiv:1911.09076v2](https://arxiv.org/abs/1911.09076v2),
§2.1, printed p.4, explicitly records the classical
Motohashi–Ramachandra estimate: for fixed $\theta>7/12$, some
$c_\theta>0$, and all sufficiently large $X$,

$$
\left|\sum_{X<n\le X+H}\mu(n)\right|
\ll_\theta H\exp\left[-c_\theta
 \left(\frac{\log X}{\log\log X}\right)^{1/3}\right]
\qquad(H\ge X^\theta).
$$

The inspected 18-page primary has SHA256
`ee94ead957a42f4be93dbba094cb601cca2fc54379bcfb84f4a8f2ad7c0d52b2`.
The formula is unnumbered and points to its reference [18], Remark 4.
This reuses the modern primary's explicit statement and attribution;
the earlier proof is not independently audited here. It is separate
from that paper's Theorem 1.1, already cited in FIB §400, which reaches
$\theta>0.55$ with a logarithmic error. The stronger exponential saving
on the longer intervals is used in the
[original-response endpoint application](../Weil/corvalan2023interpolation.md#a-paid-deletion-of-original-endpoint-responses).
The shorter interval threshold below is a different quantitative gain.

The sentence immediately following that formula on printed p.4
records the same exponential error shape for Huxley's prime number
theorem. Its quantity is fixed by equation (1.1), printed p.1:
for fixed $\theta>7/12$, the reusable statement is

$$
\left|\sum_{X<n\le X+H}\Lambda(n)-H\right|
\ll_\theta H\exp\left[-c_{\Lambda,\theta}
 \left(\frac{\log X}{\log\log X}\right)^{1/3}\right]
\qquad(H\ge X^\theta),
$$

with some $c_{\Lambda,\theta}>0$. This is the modern primary's
recorded classical input, not an independent audit of Huxley's proof.
The Möbius and prime-error constants need not agree. For the
[terminal-covariance application](../Weil/corvalan2023interpolation.md#pay-the-terminal-covariance-while-retaining-the-endpoint),
choose a smaller common constant after the scale comparisons and
restrict the bandwidth parameter accordingly. A full-prefix version
uses a fixed power margin in the length exponent; the trivial bound
for a short $\Lambda-1$ prefix costs its length times $O(\log X)$.
Neither the Möbius $0.55$ threshold nor the shorter range below is
substituted into this classical prime-error statement.

The corresponding application to the same actual CA price path, with
its pressure cost, persistence width, and exceptional-measure boundary,
is retained in [the owning Caveney note](../Arith/caveney2012sacaga.md#the-classical-huxley-rate-on-the-same-ca-price-path); this supplier note does not duplicate that application.


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

## Short-increment refinements and the retained Robin baseline

Michael Harm, *Refinements for primes in short arithmetic progressions*.

The inspected primary is [arXiv:2507.15334v2](https://arxiv.org/html/2507.15334v2),
19 May 2026, *Refinements for primes in short arithmetic progressions*.
Theorem 2.4 is a pointwise estimate for the short-interval prime-count
error $\Delta_\pi(x,y,q,a)$. Theorem 2.11 is its mean-square counterpart
over real centers $X\le u\le2X$, summed over reduced residues modulo
$q$. Both assume Conditions 1.1 and 1.2, with the stated restriction
on the zero-free-region parameter and density exponent. Their
interval-length ranges, zero-free factors and logarithmic losses
must all be retained. These are `literature-attested` inputs; neither
analytic proof is reproduced or Lean verified here.

For the ordinary prime problem take modulus $q=1$ and residue $a=1$.
The paper explicitly allows density exponent $A=30/13$ in that case
from Guth--Maynard. This letter $A$ and the paper's zero-free function
$\eta$ are separate from the Robin source's total clock $A=B+t$ and
source exponent $\eta$. Section 3.1 defines $\Delta_\pi$,
$\Delta_\vartheta$ and $\Delta_\psi$ and their conversion errors;
the theorem for $\Delta_\pi$ must not be silently substituted for a
complete-$\psi$ theorem.

In the [forward-primitive consumer PE3--PE7](../Estimation/trureturing2026pricegapconvexity.md#retain-the-compensation-while-controlling-forward-primitive-excursions),
the relevant ordinary center is the same actual real center after
any required change of variables. Its observable includes
$(v-u)E(u)$ in addition to the integrated short-increment error,
where $E(u)=u-\psi(u)$. The source's $E(A)=t+Q(A)$ is endogenous.
The cited increment theorems do not provide an estimate for that
baseline, the complete future primitive, its amplitude-integrated
exceptional occupation, or the original signed growing head.
No fixed-tolerance or density-one conclusion from this paper is
asserted to close the selected Robin comparison or prove RH.

## Effective weighted prime counts in short intervals

Jesse Thorner and Asif Zaman, *Refinements to the prime number theorem for arithmetic progressions*.

Primary source: [arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2),
version 21 September 2021, §1.1, Theorem 1.1, printed p.1.
The statement is cited directly; no proof of the published theorem or
Lean certification is supplied by this note.

For coprime integers $q\ge2$ and $a$, and $4\le h\le x$, the theorem
defines an exceptional-zero-dependent factor $\lambda$ and exponent
$\theta$. Without the exceptional real zero they are $\lambda=1$
and $\theta=7/12$. For each fixed $0<\varepsilon<1-\theta$, if
$\lambda h/\varphi(q)\ge x^{\theta+\varepsilon}$, it gives

$$
\sum_{\substack{x-h<p\le x\\p\equiv a\pmod q}}\log p
=\frac{\lambda h}{\varphi(q)}
\left[1+O_\varepsilon\left(
\exp\left\{-\frac{c_1\log x}{
\log q+(\log(x/h))^{2/3}(\log^+\log(x/h))^{1/3}
+(\log x)^{2/5}(\log\log x)^{1/5}}\right\}\right)\right].
$$

The constant $c_1=c_1(\varepsilon)>0$ and the implied constant are
effectively computable. The first product in the denominator has its
continuous zero convention at $h=x$; $\log^+u=\max\{0,\log u\}$.
The general exceptional-zero branch must not be omitted for arbitrary
moduli.

For the Robin gap application, set $q=2$, $a=1$ and
$\varepsilon=1/60$. Modulo $2$ there is no nontrivial real character,
so the exceptional-zero branch does not occur. Hence
$\lambda=1$, $\varphi(2)=1$ and
$\theta+\varepsilon=7/12+1/60=3/5$. At large interval starts all primes
in the interval are odd, so the progression sum equals the full weighted
prime sum there.

The [owning actual-gap application](../Estimation/trureturing2026pricegapconvexity.md#weighted-short-interval-counts-pay-more-actual-gap-residuals)
uses this increment estimate with an actual endpoint contact and the
existing strict first-layer activation rule. It does not use an
increment bound to erase an arbitrary complete primitive baseline.
The theorem and this note supply neither a same-source signed future
occupation/credit bound nor a Robin or RH proof.

## Uniform linear phases in a shorter range

Javier Pliego and Mengdi Wang, *Discorrelation of the Möbius function
with linear phases in short intervals*,
[arXiv:2610.11487v2](https://arxiv.org/html/2610.11487v2#S1.Thmtheorem1),
version 22 October 2026, §1, Theorem 1.1, gives, for fixed small
$\varepsilon>0$ and $X^{0.58+\varepsilon}\le H\le X$,

$$
\sup_{\alpha\in\mathbb R}
\left|\sum_{X<n\le X+H}\mu(n)e(n\alpha)\right|
\ll_\varepsilon H(\log X)^{-1/3+\varepsilon}.
$$

This theorem is unconditional. The Dirichlet-$L$ moment premise
(1.2) belongs to the paper's Theorem 1.3 on prime exponential sums;
it is not an assumption of Theorem 1.1. The statement and its
hypotheses are cited directly, without reproducing the source proof.

In the same interval range, its unconditional Theorem 1.2 gives, for
every fixed large $L\ge1$, both bounds

$$
\left|\sum_{X<n\le X+H}\Lambda(n)e(n\alpha)\right|,
\quad
\left|\sum_{X<n\le X+H}\mu(n)e(n\alpha)\right|
\le H(\log X)^{-L},
$$

unless there is an integer
$1\le q\ll(\log X)^{O_L(1)}$ with

$$
\|q\alpha\|\ll\frac{X(\log X)^{O_L(1)}}{H^2}.
$$

This is a minor-arc input, including for the uncentered prime sum;
it does not give an arbitrary-logarithmic bound at every phase.
The zero phase is exceptional with $q=1$. The same allowed major-arc
scale contains $|\alpha|\le1/H$, since $H\le X$ implies
$1/H\le X/H^2$. A weighted Fourier transfer must therefore retain
this slow-frequency contribution together with its actual baseline,
expansion weight and losses. Theorem 1.3 reduces the exception width
to $(\log X)^{O_L(1)}/H$ only under the stated fourth-moment premise
(1.2); zero frequency remains exceptional there too.

For the [original residual-band application (I59)](../Weil/corvalan2023interpolation.md#pay-the-terminal-covariance-while-retaining-the-endpoint),
$X\asymp N$ and $H\asymp N^{3/4}e^{\lambda\Omega(N)}$ satisfy
this length range eventually. At this length, however, the previously
cited Theorem 1.2 of arXiv:2610.09567v1 already supplies arbitrary
fixed logarithmic savings for linear phases, realized as fixed
one-dimensional torus nilsequences with uniform Lipschitz bounds.
For the untwisted phase the longer-interval exponential error above
is also stronger. The shorter admissible length in this new source
does not improve the error supplied for that particular family.

The residual moments and endpoint in (I56) are not a single linear
phase. Turning them into a phase superposition still requires a proved
expansion, its total weight and all losses, with the same actual
coefficients and endpoint retained. Likewise the smooth test in
(I78)--(I82) has growing derivative costs and two exact arithmetic
scalar channels. This cited theorem supplies neither their joint
cancellation nor a complete signed Robin estimate.
