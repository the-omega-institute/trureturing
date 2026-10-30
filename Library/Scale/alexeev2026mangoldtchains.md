---
bibkey: alexeev2026mangoldtchains
authors: Boris Alexeev; Kevin Barreto; Yanyang Li; Jared Duker Lichtman; Liam Price; Jibran Iqbal Shah; Quanyu Tang; Terence Tao
year: 2026
title: "Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond"
doi: 10.48550/arXiv.2605.00301
url: https://arxiv.org/abs/2605.00301v1
claim: Lemmas 3.2 and 3.3(ii) supply unconditional positive-kernel upper bounds. Section 10.2 supplies the zeta process; its finite-divisor cut exposes the divisor sum as an endpoint density. Neither application supplies the signed Robin estimate at the original CA source.
strata_touched: []
license: citation-only
triage: anchor
---

# Positive von Mangoldt kernels and the remaining localization problem

The inspected primary is [arXiv:2605.00301v1](https://arxiv.org/pdf/2605.00301v1),
submitted 1 May 2026, with 35 printed pages. The bounds and their proofs
in §3.1, printed pp.12–16, the invariant weight in Example 2.8, printed
pp.9–10, and the zeta process in §10.2, printed p.31, are reused.
The paper proves results about
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

## The existing zeta process on the actual finite divisor cut

Example 2.8, equation (2.9), gives the invariant weight

$$
\nu_\Lambda(1)=1,\qquad
\nu_\Lambda(n)=\int_1^\infty
            \frac{\log n}{\zeta(s)n^s}\,ds\quad(n>1)
$$

for the downward transition
$P(n\to n/q)=\Lambda(q)/\log n$, where $q\mid n$ and $q>1$.
Section 10.2 realizes it by a common divisibility chain $Z_s$ with
$\mathbb P(Z_s=n)=1/(\zeta(s)n^s)$ for $s>1$. Both the chain and
invariant measure are existing constructions, not new FIB processes.

For the same actual integer $N$, take its finite divisor ideal
$\mathcal D_N=\{d:d\mid N\}$ and put

$$
F_N(s)=\sum_{d\mid N}d^{-s},\qquad
Q_N(s)=\mathbb P(Z_s\mid N)=\frac{F_N(s)}{\zeta(s)}.
\tag{VM6}
$$

Write $a_p=v_p(N)$, including $a_p=0$ outside the finite support.
The Euler product is
$Q_N(s)=\prod_p(1-p^{-(a_p+1)s})$. Thus it retains the actual finite
exponents, as well as all primes outside the support. Its cut flux is

$$
Q_N'(s)=\frac1{\zeta(s)}
 \sum_{d\mid N}\ \sum_{\substack{q\ge2\\dq\nmid N}}
       \frac{\Lambda(q)}{(dq)^s}\ge0\qquad(s>1).
\tag{VM7}
$$

Indeed the internal transition sum is
$\sum_{m\mid N}(\log m)m^{-s}=-F_N'(s)$, using the classical identity
$\sum_{q\mid m}\Lambda(q)=\log m$. Subtracting it from
$-F_N(s)\zeta'(s)/\zeta(s)$ gives (VM7) after division by $\zeta(s)$.
All sums are absolutely convergent for $s>1$.

The pole of $\zeta$ at $1$ and the limits at infinity now give

$$
Q_N(1+)=0,\qquad Q_N(\infty)=1,\qquad
\int_1^\infty Q_N'(s)\,ds=1,\qquad
Q_N'(1+)=F_N(1)=\frac{\sigma(N)}N.
\tag{VM8}
$$

This is the source's invariant-flow conservation applied to a finite
divisor ideal. The conserved mass is $1$ for every $N$; the Robin
quantity is instead the endpoint density $Q_N'(1+)$. In particular,
unit mass alone does not bound that density: the positive densities
$b e^{-b(s-1)}$ on $s>1$ have mass $1$ and endpoint value $b$ for
arbitrary $b>0$. This elementary comparison concerns general densities;
it is not an arithmetic counterexample or a substitute source.

To retain the original signed-tail obligation exactly, put
$A=\log N$, $L=\log A$ and
$h_N=\log G(N)-\gamma$. On the same retained regular sources,
$I_\psi(A)=-h_N-R_{\rm CA}(A)$, so its fixed-floor target reads

$$
\log\!\left(\frac{Q_N'(1+)}{e^\gamma L}\right)
 +R_{\rm CA}(A)
\le\frac{M}{\sqrt A\,L}.
\tag{VM9}
$$

Here $M$ must be fixed uniformly over all sufficiently large retained
sources. Equation (VM9) is the existing obligation in these
coordinates, not an established estimate. The invariant flow and
normalization (VM8) do not supply it. A new use of the joint GA1,
CA and full future-record constraints would have to control this
endpoint and the same source's full reserve together. Neither replacing
the cut by the minimal nondivisors nor omitting prime-power jumps
preserves the full flux (VM7).
