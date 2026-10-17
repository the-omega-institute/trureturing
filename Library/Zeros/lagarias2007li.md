---
bibkey: lagarias2007li
authors: Jeffrey C. Lagarias
year: 2007
title: Li Coefficients for Automorphic L-Functions
doi: 10.5802/aif.2311
claim: The pole-removed completed automorphic L-function is entire of order one; the trivial representation gives twice the classical Riemann xi function.
strata_touched:
  - D5/S3/Analytic/Resolvent/XiGlobalGrowth
license: citation-only
triage: anchor
---

# Li Coefficients for Automorphic L-Functions

Theorem 2.1(6) states that the pole-removed function `xi(s, pi)` is entire
of order one and maximal type. Its standing hypothesis is an irreducible
cuspidal unitary automorphic representation over the rationals. The paragraph
immediately before Theorem 2.1 explicitly includes the trivial representation
of GL(1), for which `xi(s, pi_triv) = 2 xi(s)`. The simple poles at zero and
one have been removed in this normalization.

Consequently, for the classical xi function there is a positive real constant
C such that `|xi(s)| <= exp(C (1 + |s|)^(3/2))` for every complex s. This is a
weaker consequence of order one, not the literal statement of Theorem 2.1(6).
The factor two and a bounded initial disk can be absorbed into C. No Riemann
hypothesis is required for this consequence.

`D5/S3/Analytic/Resolvent/XiGlobalGrowth.xi_reading_norm_le_exp_log_linear` proves
the stronger bound `exp(C (1 + |s|) (1 + log(1 + |s|)))` directly from the
existing symmetric theta-Mellin integral. The normalized resolvent derives the
displayed three-halves consequence inside its proof.
It does not formalize automorphic representations, an order-one theorem,
Hadamard factorization, or the paper's Li coefficient identities. Its private
integrand estimate keeps an unspecified positive theta decay rate and the
whole initial integration interval. The actual Lean xi is the global
pole-removed definition, including its values at zero and one.

## Verified locator

- Read on 2026-09-09: https://arxiv.org/html/math/0404394, the normalization
  preceding Theorem 2.1, all six clauses of the theorem, and its proof of (6).
  The proof treats the trivial representation's poles explicitly. Its later
  informal statements about the meromorphic completion are not used as
  formulas at the two poles.
- Crossref's exact author/title query on 2026-09-09 matched Jeffrey C. Lagarias,
  this title, and DOI https://doi.org/10.5802/aif.2311.
- Published in Annales de l'Institut Fourier 57 (2007), 1689–1740.

## Fibonacci-only Li sampling: a general-model obstruction

This section is a repository application of an existing Fibonacci avoidance
theorem and the standard Fejer kernel identity, not a theorem attributed to
Lagarias. It concerns general symmetric zero models, not the actual zeta
function. It is a paper derivation without Lean certification or a priority
claim. The Li conventions are those in arXiv:math/0404394v4, Introduction,
equations (1.1)–(1.3) and the general multiset discussion following (1.6).

### FL1. Reused explicit Fibonacci avoidance

Set $F_0=0$, $F_1=1$, and $F_{j+2}=F_{j+1}+F_j$. The distinct positive
Fibonacci indices are $F_2,F_3,\ldots=1,2,3,5,\ldots$.
Victoria Zhuravleva, *Diophantine approximations with Fibonacci numbers*,
[arXiv:1112.6142v1](https://arxiv.org/abs/1112.6142v1), Theorem 2,
supplies the explicit choice

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\alpha=\frac1{\varphi+2},\qquad
\delta=\frac{\varphi-1}{\varphi+2}>0.
$$

For every $N\ge4$, the theorem states
$\min_{1\le j\le N}\|F_j\alpha\|_{\mathbb R/\mathbb Z}=\delta$.
In particular $\alpha$ is irrational, $0<\delta<1/2$, and

$$
\|F_j\alpha\|_{\mathbb R/\mathbb Z}\ge\delta\qquad(j\ge2).
$$

The theorem is reused without a new proof. Peres–Schlag's general
lacunary avoidance theorem, already cited in
[the lacunary-source discussion](../Dynamics/iyer2025empirical.md),
also gives a suitable multiplier, but the explicit Fibonacci result
supplies this application's input directly. No optimality or winning-set
claim from either source is needed.

### FL2. A strict sign on every Fibonacci index

Choose an integer $D\ge1$ with $D+1>\csc^2(\pi\delta)$, and put

$$
m_k=D+1-k\quad(1\le k\le D),\qquad
T=\sum_{k=1}^D m_k=\frac{D(D+1)}2,\qquad
S_n=\sum_{k=1}^D m_k\cos(2\pi kn\alpha).
$$

The standard Fejer identity gives

$$
2S_n=
\frac{\sin^2((D+1)\pi n\alpha)}{\sin^2(\pi n\alpha)}-(D+1).
$$

Consequently, with
$\eta=((D+1)-\csc^2(\pi\delta))/2>0$,

$$
S_{F_j}\le-\eta\qquad(j\ge2).
$$

All multiplicities $m_k$ are positive integers. The same $D$, $\alpha$
and $\eta$ work for every sampled index.

### FL3. Off-line zeros inside the strip

Irrationality gives $\cos(2\pi k\alpha)<1$ for every $1\le k\le D$.
Choose one fixed $r>1$ sufficiently close to one that
$r\cos(2\pi k\alpha)<1$ for all these $k$. Define

$$
z_k=r e^{2\pi i k\alpha},\qquad \rho_k=\frac1{1-z_k},
$$

and form the multiset $Z$ with the quartet
$\rho_k,\overline{\rho_k},1-\rho_k,1-\overline{\rho_k}$,
each repeated $m_k$ times. Writing $\theta_k=2\pi k\alpha$,

$$
\Re\rho_k=\frac{1-r\cos\theta_k}{1-2r\cos\theta_k+r^2},\qquad
\Re\rho_k-\frac12=\frac{1-r^2}{2|1-z_k|^2}<0.
$$

The numerator of the first fraction is positive; its denominator minus
its numerator is $r(r-\cos\theta_k)>0$. Thus every member of $Z$ lies
strictly in $0<\Re s<1$, none lies on $\Re s=1/2$, and none is zero or
one. Irrationality also makes these roots nonreal.

Let $P(s)=\prod_{\rho\in Z}(s-\rho)$, with multiplicities. This monic
polynomial has real coefficients, degree $4T$, $P(1-s)=P(s)$, and
$P(s)>0$ on the real axis. Define its finite Li sums by

$$
L_n(P)=\sum_{\rho\in Z}\left[1-\left(1-\frac1\rho\right)^n\right].
$$

The four Mobius values from each quartet are
$z_k,\overline{z_k},z_k^{-1},\overline{z_k}^{-1}$. Hence

$$
L_n(P)=4T-2(r^n+r^{-n})S_n,
$$

and therefore

$$
L_{F_j}(P)\ge4T+2\eta(r^{F_j}+r^{-F_j})>0\qquad(j\ge2).
$$

For an individual root, the Li derivative at $s=1$ gives the inverse
power $1-(1-1/\rho)^{-n}$. Reflection symmetry makes the full sum
invariant under $n\mapsto-n$. Thus $L_n(P)$ also equals

$$
\frac1{(n-1)!}
\left.\frac{d^n}{ds^n}\bigl[s^{n-1}\log P(s)\bigr]\right|_{s=1}
\qquad(n\ge1),
$$

using the local real logarithm. A constant normalization has no effect.
This retains the distinction between the two conventions in Lagarias's
Introduction rather than identifying individual-root formulas.

There is an unbounded sequence of positive integers $n_l$ with
$\|n_l\alpha\|_{\mathbb R/\mathbb Z}\to0$, by irrational rotation
recurrence. Along it, $S_{n_l}\to T>0$, so $L_{n_l}(P)<0$ eventually.
Thus the positive Fibonacci samples coexist with negative unsampled
coefficients; the complete all-index criterion is unchanged.

### FL4. Entire order one and infinitely many zeros

Put $H(s)=P(s)\cosh(s-1/2)$. It is entire of order exactly one, has real
values and is strictly positive on the real axis, satisfies
$H(1-s)=H(s)$, and has no zeros at zero or one. Its added zeros are
$1/2\pm it_h$, where $t_h=\pi(h+1/2)$ and $h\ge0$.

The standard paired cosh product gives the exact normalization

$$
\frac{\cosh(s-1/2)}{\cosh(1/2)}
=\prod_{h\ge0}\left(1+\frac{s^2-s}{1/4+t_h^2}\right).
$$

It converges locally uniformly, with no unrecorded exponential factor.
For $u_h=1-1/(1/2+it_h)$, $|u_h|=1$, so the paired Li contribution is

$$
L_n(\cosh)=\sum_{h\ge0}2(1-\Re u_h^n),\qquad
0\le L_n(\cosh)\le n^2\sum_{h\ge0}\frac1{1/4+t_h^2}.
$$

The bound follows from $|1-u^n|\le n|1-u|$ on the unit circle and
$|1-u_h|^2=(1/4+t_h^2)^{-1}$. It proves absolute convergence after
conjugate pairing for each fixed $n$. Local logarithmic differentiation
of the displayed product identifies the paired sums with its Li
derivatives. Consequently $L_n(H)=L_n(P)+L_n(\cosh)$: every Fibonacci
sample remains positive, while the negative exponential term along
$n_l$ eventually dominates the nonnegative $O(n_l^2)$ added term.

### FL5. What this excludes

Fibonacci-index positivity cannot replace all-index positivity on this
general zero-model class, even with conjugation symmetry, functional
symmetry, open-strip confinement, entire order one, and infinitely many
zeros. A zeta-specific conclusion requires input beyond these properties;
this argument does not identify sufficient additional analytic or
arithmetic input. No Euler product or zeta explicit formula for $H$ is
established. This model is not a counterexample to RH, Robin, or a
zeta-specific sparse criterion. No numerical experiment or zero computation
is used.

This restriction of tested indices is distinct from using Fibonacci or
Zeckendorf addresses to label all integer indices. Such an all-index
encoding does not discard indices and is not excluded by this example.
