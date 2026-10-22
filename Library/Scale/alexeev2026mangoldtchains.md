---
bibkey: alexeev2026mangoldtchains
authors: Boris Alexeev; Kevin Barreto; Yanyang Li; Jared Duker Lichtman; Liam Price; Jibran Iqbal Shah; Quanyu Tang; Terence Tao
year: 2026
title: "Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond"
doi: 10.48550/arXiv.2605.00301
url: https://arxiv.org/abs/2605.00301v1
claim: Lemmas 3.2 and 3.3(ii) supply unconditional positive-kernel upper bounds. Their application to the Diamond–Ford error controls a full-domain smoothed integral, not the signed Robin tail at the original CA source.
strata_touched: []
license: citation-only
triage: anchor
---

# Positive von Mangoldt kernels and the remaining localization problem

The inspected primary is [arXiv:2605.00301v1](https://arxiv.org/pdf/2605.00301v1),
submitted 1 May 2026, with 35 printed pages. The bounds and their proofs
in §3.1, printed pp.12–16, are reused. The paper proves results about
primitive sets and divisibility chains; no RH conclusion is attributed
to it. This note records a parameter correspondence and its limits,
not a new estimate, novelty claim or Lean verification.

## The existing positive-kernel bounds

Lemma 3.2, equation (3.1), gives, for every real $u>0$,

$$
\sum_{n\ge2}\frac{\Lambda(n)}{n^{1+u}}
=-\frac{\zeta'(1+u)}{\zeta(1+u)}
\le\frac{\log2}{2^u-1}\le\frac1u.
\tag{VM1}
$$

The source derives the middle bound from the known monotonicity of
the Dirichlet eta function. Lemma 3.3(ii), equation (3.7), gives, for
$m=2^v$ with $v\ge1$,

$$
(\log m)\sum_{n\ge2}\frac{\Lambda(n)}{n\log^2(mn)}
\le\sum_{j\ge1}\frac{v}{(v+j)^2}
\le\frac{v}{v+1/2}.
\tag{VM2}
$$

Here $v$ can be real: the source's proof uses (VM1), Tonelli's theorem,
and convexity of $t\mapsto v/(v+t)^2$; no integer power of $2$ is
required. Consequently $h=\log m$ ranges over all real
$h\ge\log2$. With $c=(\log2)/2$, (VM2) reads

$$
\sum_{n\ge2}\frac{\Lambda(n)}{n(h+\log n)^2}
\le\frac1{h+c}.
\tag{VM3}
$$

This uses the existing proof on its real parameter domain; it
requires neither interpolation nor a new discrete-to-continuous
estimate. In particular, $h=\log A$ is allowed for every real $A\ge2$.

## Application to the Diamond–Ford error

Use the [existing Diamond–Ford notation](diamondford2008generalizedeuler.md):

$$
R_{\rm DF}(t)=\sum_{n\le t}\frac{\Lambda(n)}n-\log t+\gamma,
\qquad t\ge1.
$$

The sum is zero on $[1,2)$, so $R_{\rm DF}(1)=\gamma$.
Partial summation with weight $(h+\log t)^{-2}$ gives

$$
\sum_{n\ge2}\frac{\Lambda(n)}{n(h+\log n)^2}
=\frac1h-\frac\gamma{h^2}
 +2\int_1^\infty
       \frac{R_{\rm DF}(t)}{t(h+\log t)^3}\,dt.
\tag{VM4}
$$

The lower boundary term vanishes because the partial sum at $1$ is
zero; Mertens' estimate makes the upper boundary term vanish.
The explicit contributions use
$2\int_0^\infty v(h+v)^{-3}dv=1/h$ and
$2\int_0^\infty(h+v)^{-3}dv=1/h^2$.
Thus the application of (VM3) is

$$
2\int_1^\infty\frac{R_{\rm DF}(t)}{t(h+\log t)^3}\,dt
\le\frac\gamma{h^2}-\frac{c}{h(h+c)},
\qquad h\ge\log2.
\tag{VM5}
$$

This is an unconditional **upper** bound on a smoothed integral over
the full interval $[1,\infty)$. Choosing $h=\log A$ keeps the portion
$1\le t<A$ and does not turn it into
$K_{\rm DF}(A)=\int_A^\infty R_{\rm DF}(t)/(t\log^2t)\,dt$.
Since $R_{\rm DF}$ is signed, neither discarding that initial portion
nor comparing the two positive kernels preserves an inequality
without further information about $R_{\rm DF}$.

The [original same-source Robin obligation](../Arith/caveney2012sacaga.md#retain-the-original-oscillation-exponent-on-the-regular-ga1-source)
is an eventual fixed lower bound on
$\sqrt A\log A\,I_\psi(A)$ at $A=\log N$ for the retained jointly
proper-GA1, event-free own-price CA, all-integer future-record sources.
The DF comparison still involves both $R_{\rm DF}(A)$ and
$K_{\rm DF}(A)$ at this same $A$. The source's positive-kernel bounds
do not by themselves supply that joint lower estimate or remove the
full CA reserve. A localization and signed comparison remains unpaid.
