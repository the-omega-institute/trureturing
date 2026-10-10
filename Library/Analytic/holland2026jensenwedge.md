---
bibkey: holland2026jensenwedge
authors: Jonathan Holland
year: 2026
title: A new hyperbolicity wedge and a joint semicircle limit for Jensen polynomials of Riemann's xi-function
doi: null
url: https://arxiv.org/abs/2608.08682v1
claim: Theorem 1.1 states a joint degree-shift hyperbolicity region for the actual xi coefficients; its sufficient condition excludes every positive degree at zero shift.
strata_touched: []
license: citation-only
triage: anchor
---

# A joint degree-shift Jensen supplier

The primary is [arXiv:2608.08682v1](https://arxiv.org/html/2608.08682v1),
Jonathan Holland, *A new hyperbolicity wedge and a joint semicircle limit
for Jensen polynomials of Riemann's xi-function*. The source locators
below refer to this version. Its coefficient definitions, Theorem 1.1,
Proposition 2.2, Lemmas 8.1 and 9.1, and the completion of the argument
in section 10 were inspected. The results remain public-preprint
statements; this note supplies neither a complete independent proof
audit nor Lean verification. No source text is vendored.

## Source coefficients and the joint region

Section 1 uses the standard completed function

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad
\xi(1/2+z)=\sum_{k\ge0}\frac{\Gamma_k}{k!}z^{2k}.
$$

Here $\Gamma_k$ denotes the paper's positive coefficient $\gamma(k)$,
not a value of the Euler Gamma function. For integers $d,n\ge0$ it defines

$$
J^{d,n}(X)=\sum_{k=0}^{d}\binom dk\Gamma_{n+k}X^k.
$$

Theorem 1.1 states that there is an absolute constant $K>0$ such that

$$
d\ge1,\quad n\ge0,\quad n^3\log^2(n+2)\ge Kd^5
\quad\Longrightarrow\quad
J^{d,n}\text{ has }d\text{ distinct negative real roots}.
\tag{JW}
$$

Equivalently the sufficient region has
$d\le K^{-1/5}n^{3/5}\log^{2/5}(n+2)$. It permits degree and shift
to grow together. The existence of $K$ does not supply a numerical
threshold or a finite-input certificate. The statement is unconditional
within its sufficient region; it is not a statement for every pair
$(d,n)$.

The source's proof compares the actual coefficient ratios with a
positive-root model formed from Laguerre and Jacobi families and
finite-free multiplicative convolution. Proposition 2.2 supplies its
multiplier stability step; the comparison matches coefficients through
index four. Lemma 8.1 bounds the remaining multiplier error by

$$
O\!\left(\frac{d^{5/2}}{n^{3/2}\log(n+2)}\right),
$$

on its specified complex neighborhood, and Lemma 9.1 controls derivative
ratios at the comparison model's critical points. Section 10 combines
these estimates to obtain (JW). These are source results to reuse,
not new polynomial identities or estimates of this repository.

The five coefficient matching conditions concern the actual xi sequence.
They do not identify the five Zeckendorf inclusion modes
`[null,2,3,2 5,5]` with these moments or supply an estimate through that
encoding. Such an application would require its own parameter and
inequality correspondence.

## Correspondence with the actual theta coefficients

Use the original full-axis theta representation in
[Romik's owning note](romik2021orthogonal.md), with
$\Xi(z)=\xi(1/2+iz)$ and
$\Xi(z)=\int_{\mathbb R}\Phi(t)e^{izt}\,dt$. The actual normalized
coefficients are

$$
a_k=\frac{\int_{\mathbb R}t^{2k}\Phi(t)\,dt}
           {(2k)!\,\Xi(0)},
\qquad a_0=1,
\qquad \Gamma_k=\Xi(0)\,k!\,a_k.
\tag{TC}
$$

The last equality uses the even Taylor expansion of
$\xi(1/2+z)=\Xi(-iz)$ under the original transform. It keeps the full
theta kernel and its central-value normalization. It neither replaces
the source by an arbitrary positive measure nor identifies positive
theta-moment Hankel matrices with matrices of actual root power sums.
These are paper-level source correspondences. In the repository's
moment interface, normalization from $a_0=1$ is a conditional result;
this note is not a new Lean proof discharging that hypothesis or
transporting Holland's theorem to `xiReading`.

For $d\ge1$ the source polynomial and its shifted analogues are

$$
\begin{aligned}
P_d(X)&=\frac{J^{d,0}(X/d)}{\Xi(0)}
       =\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kX^k,\\
\mathcal P_{d,n}(X)&=\frac{J^{d,n}(X/d)}{\Gamma_n}
       =\sum_{k=0}^{d}\frac{(d)_k}{d^k}b_k^{(n)}X^k,\\
b_k^{(n)}&=\frac{\Gamma_{n+k}}{k!\,\Gamma_n},
\qquad b_0^{(n)}=1.
\end{aligned}
\tag{PN}
$$

Here $(d)_k=d(d-1)\cdots(d-k+1)$ is the falling factorial, with
$(d)_0=1$. Reflecting $\mathcal P_{d,n}(-X)$ at degree $d$ gives
the constant

$$
\beta_{d,n}=(-1)^d\frac{\Gamma_{n+d}}{d^d\Gamma_n},
\qquad
\beta_{d,0}=(-1)^d\frac{d!}{d^d}a_d=\beta_d.
\tag{BC}
$$

Only $n=0$ recovers the original $a_k$ and $\beta_d$. Changing $n$
changes the actual coefficient window and its integration constant;
it is not a coordinate change of the same $P_d$.

## Reuse and the remaining zero-shift obligation

The existing
[canonical normalization and degree-lowering interface](../../Blueprint/D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.md),
[source primitive and constant](../../Blueprint/D5/S3/Zeros/Jensen/SourceJensenIntegralExtension.md),
[source residue criterion](../../Blueprint/D5/S3/Zeros/Jensen/SourceJensenPositiveExtension.md),
and [total coupling budget](../../Blueprint/D5/S3/Zeros/Jensen/SourceJensenCouplingBudget.md)
are the corresponding repository interfaces. Their hypotheses and
scope remain those of the owning sources. Equations (TC), (PN) and
(BC) specify the literature parameters; they do not warrant new
binding-only wrappers or a repeated derivation of these interfaces.

For every $d\ge1$, substituting $n=0$ into (JW) gives a zero left
side and a strictly positive right side. Thus this sufficient condition
covers no positive degree at zero shift. This excludes an application
of (JW), not real-rootedness of those polynomials. In particular,
degree-growing hyperbolicity at large shifts does not furnish a bound
on the original zero-shift integration constants.

For $d\ge2$, in the existing primitive notation, $q_d$ is the degree-$d$ reflection
of $P_d(-X)$, $\alpha_d=(d-1)/d$, and

$$
q_d(x)=R_d(x)+\beta_d,
\qquad
R_d(x)=\int_0^x d\alpha_d^{d-1}
                   q_{d-1}(u/\alpha_d)\,du.
$$

To extend a source polynomial upward, one still needs a joint estimate
of its actual $\beta_d$, critical nodes, and values of $R_d$ at those
nodes. Equivalently, under source normalization $a_0=1$ and the
distinct-positive-preceding-root hypotheses of the existing residue
criterion, the individual source
residues must be nonnegative. Their total coupling budget does not
establish every individual sign. Holland's shifted region supplies
no zero-shift, unbounded-degree estimate of these quantities.

The note does not assert a largest known finite-degree range or
exhaustive coverage of the Jensen literature. Its reusable input is
the versioned joint region (JW) with the exact source correspondence.
It supplies no new RH conclusion, signed Robin-tail estimate, or
quantitative moment inequality from FIB ATOM geometry.
