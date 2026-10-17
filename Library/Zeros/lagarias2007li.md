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

## Fibonacci-sampled absolute growth: a paper criterion

Fibonacci-only sign positivity in FL1–FL5 differs from an absolute-growth
condition. The following paper derivation gives

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\limsup_{j\to\infty}|\lambda_{F_j}|^{1/F_j}\le1,
\qquad F_0=0,\ F_1=1,
\tag{FG1}
$$

for the actual classical Li coefficients. It does not establish the
displayed growth bound for those coefficients and therefore does not
prove RH. No Lean certification or literature priority is claimed.
Hilbert basis, Laurent observation ideals and the Li generating-function
identity are existing tools; the application and its remaining bound
must be distinguished from them.

### FG2. A finite exact relation for the common Fibonacci phase state

Fix $d\ge1$ and positive integers $m_1,\ldots,m_d$; write $M=\sum_i m_i$.
Work in the Noetherian Laurent polynomial ring

$$
\mathcal A=\mathbb Q[X_1^{\pm1},\ldots,X_d^{\pm1},
                         Y_1^{\pm1},\ldots,Y_d^{\pm1}].
$$

Noetherianity is the usual finite-type extension and localization result;
see [Stacks Project, Lemma 10.31.1, tag 00FN](https://stacks.math.columbia.edu/tag/00FN).
It imposes no algebraicity condition on the points where these formal
polynomial identities are evaluated.

The Fibonacci phase update and its inverse are

$$
T(x,y)=(y,xy),\qquad T^{-1}(x,y)=(y/x,x),
$$

coordinatewise. Pullback $\sigma f=f\circ T$ is a ring automorphism,
with $\sigma X_i=Y_i$ and $\sigma Y_i=X_iY_i$. Put
$p=\sum_i m_iX_i$ and $I=(p,\sigma p,\sigma^2p,\ldots)$.
The inclusion $\sigma I\subseteq I$ gives the ascending ideal chain

$$
I\subseteq\sigma^{-1}I\subseteq\sigma^{-2}I\subseteq\cdots.
$$

It stabilizes by Noetherianity. Applying a power of $\sigma$ at a
stabilization gives $\sigma I=I$. In particular, ideal membership
supplies some finite $K\ge1$ and $a_1,\ldots,a_K\in\mathcal A$ with

$$
\boxed{\ p=\sum_{r=1}^K a_r\,\sigma^rp.\ }
\tag{FG2}
$$

This is an identity before any phases are substituted. No effective
value of $K$ or bound on the coefficients is computed here.

### FG3. Every fixed-length block retains a nonzero observation

Let $u_i\in\mathbb S^1$, put $a=(1,\ldots,1,u_1,\ldots,u_d)$, and
use the same state for every iterate. Then

$$
T^ja=((u_i^{F_j})_i,(u_i^{F_{j+1}})_i),\qquad
q_j=p(T^ja)=\sum_i m_i u_i^{F_j},\qquad q_0=M>0.
$$

Every Laurent monomial has modulus one on
$\mathbb T=(\mathbb S^1)^{2d}$. Let
$C=\max(1,\sum_{r=1}^K\|a_r\|_1)$, where the norm is the sum of
absolute coefficient values. Evaluating FG2 at $T^ja$ gives

$$
|q_j|\le C\max_{1\le r\le K}|q_{j+r}|.
$$

For $B_j=\max_{0\le r<K}|q_{j+r}|$, this yields
$B_j\le CB_{j+1}$: all entries except the first already belong to
the next block. Thus

$$
\boxed{\ \max_{0\le r<K}|q_{j+r}|\ge MC^{-j}\qquad(j\ge0).\ }
\tag{FG3}
$$

Both $K$ and $C$ depend only on the fixed multiplicity vector, not on
the phases or $j$. Positivity enters through $q_0=M$. Repeated phases,
root-of-unity ratios and simultaneous dominant zeros are retained.
No single dominant pair or algebraicity assumption is used.

The update is the multiplicative phase form of the matrix
$\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$, with
initial exponent pair $(0,1)$. Its invertibility is essential to FG2.
The scalar update $u\mapsto u^2$ has no inverse in the Laurent ring;
there is no corresponding assertion for arbitrary lacunary sequences.

### FG4. Finite positive power sums preserve their maximal root rate

Let $z_i\ne0$ be arbitrary complex bases with positive integer weights
$m_i$, allowing repetitions, and set $R=\max_i|z_i|$. Then

$$
\limsup_{j\to\infty}
\left|\sum_i m_i z_i^{F_j}\right|^{1/F_j}=R.
\tag{FG4}
$$

For common modulus $R$, write $z_i=Ru_i$ and use FG3. Every block
supplies an index $\ell_j\in[j,j+K-1]$ with
$|q_{\ell_j}|\ge MC^{-j}$. Since $j/F_{\ell_j}\to0$, this loss has
root rate one on the scale $F_{\ell_j}$. The elementary bound
$|q_j|\le M$ gives the reverse inequality.

More generally, for dominant bases $|z_i|=R$ and any remainder
$E_n=O(B^n)$ with a fixed $0<B<R$, the same proof gives

$$
a_n=-\sum_i m_i z_i^n+E_n
\quad\Longrightarrow\quad
\limsup_j|a_{F_j}|^{1/F_j}=R.
\tag{FG5}
$$

Writing $|E_n|\le AB^n$ for sufficiently large $n$, at the indices supplied by FG3,
$|a_{F_{\ell_j}}|\ge R^{F_{\ell_j}}(MC^{-j}-A(B/R)^{F_{\ell_j}})$,
which is at least $MC^{-j}R^{F_{\ell_j}}/2$ eventually.
Unequal-modulus sums in FG4 follow by placing all smaller-modulus
terms in this remainder. The bound holds in every block; the favorable
indices are consequences, not an assumption about a selected subsequence.

### FG5. The actual Li generating function pays the entire remainder

Use Lagarias, arXiv:math/0404394v4, Introduction, equation (1.4):

$$
G(w)=-\frac1{(1-w)^2}
 \frac{\xi'}{\xi}\!\left(-\frac{w}{1-w}\right)
=\sum_{n\ge1}\lambda_nw^{n-1}.
\tag{FG6}
$$

This is the logarithmic derivative of the actual composed xi function,
not a global choice of logarithm or a substituted zero model. Xi is
entire and nonzero at zero, so $G$ is holomorphic near zero and
meromorphic throughout $|w|<1$.

A zero $\rho$ of multiplicity $m_\rho$ gives a simple pole at
$w_\rho=\rho/(\rho-1)$, with residue $m_\rho$. Put
$z_\rho=1-1/\rho=1/w_\rho$. Its pole term is

$$
\frac{m_\rho}{w-w_\rho}
=-\frac{m_\rho z_\rho}{1-z_\rho w}
=-\sum_{n\ge1}m_\rho z_\rho^n w^{n-1}.
\tag{FG7}
$$

If RH is false, reflection symmetry supplies a zero with
$\Re\rho<1/2$, hence a pole inside the disk since
$|z_\rho|^2=1+(1-2\Re\rho)/|\rho|^2>1$.
The discrete pole set has a positive smallest modulus $r_0<1$, attained
at finitely many poles $w_1,\ldots,w_d$. Retain all their multiplicities
$m_i>0$ and put $z_i=1/w_i$, $R=1/r_0>1$.

Choose $r_0<r_1<1$ so these are the only poles in $|w|\le r_1$.
Subtracting all their principal parts gives

$$
H(w)=G(w)+\sum_{i=1}^d\frac{m_i z_i}{1-z_iw},
$$

holomorphic on a neighborhood of the closed disk $|w|\le r_1$.
Cauchy's coefficient estimate for $H$ gives the exact decomposition

$$
\lambda_n=-\sum_{i=1}^d m_i z_i^n+E_n,\qquad
E_n=O(B^n),\qquad B=1/r_1<R.
\tag{FG8}
$$

This controls the entire analytic remainder of the actual generating
function. It neither discards uncomputed zeros nor rearranges an infinite
constant-minus-power sum. No zero-height computation is required.
By the smaller-remainder estimate (FG5), under RH failure,

$$
\limsup_j|\lambda_{F_j}|^{1/F_j}
=\max_\rho\left|1-\frac1\rho\right|>1.
\tag{FG9}
$$

Conversely, under RH the same $G$ has no poles inside the unit disk.
The standard Cauchy coefficient bound on every smaller disk gives the
all-index root bound, hence its Fibonacci restriction. This is the known
RH-to-growth implication, also recorded in Lagarias's all-index criterion
(Theorem 2.2(3), equation (2.22)); it is reused, not counted as new
mathematics. Together with FG9 it gives FG1.

### FG6. What remains to prove

The unpaid assertion is still the actual bound
$|\lambda_{F_j}|=O_\varepsilon(e^{\varepsilon F_j})$ for every
$\varepsilon>0$. The exact finite observation relation detects an
exponential rate; it does not rule that rate out for the actual xi
function. FL1–FL5 remains a valid sign-only obstruction, whose positive
Fibonacci samples grow exponentially. The original Robin signed estimate,
the endpoint half-variance bound and RH remain unresolved. No numerical
experiment, parameter scan, zero computation or new Lean certification
is used.

## A signed truncation formula requires a source-use restriction

Theorem 6.1, equation (6.2), in both arXiv:math/0404394v4 and the
[published article](https://aif.centre-mersenne.org/item/10.5802/aif.2311.pdf),
printed p.1722, is not adopted here as an unconditional signed supplier.
With the article's definition

$$
L_n(T)=\sum_{\substack{\rho\in Z(\zeta)\\|\Im\rho|\le T}}
\left[1-\left(1-\frac1\rho\right)^n\right],
$$

including all zero multiplicities, that displayed formula reads
$S_f(n)=+L_n(\sqrt n)+O(\sqrt n\log n)$. The following local
residue and consistency checks explain the restriction; they do not
establish that the printed statement is false.

For the counterclockwise contour in the proof, with normalization
$1/(2\pi i)$, put $k_n(s)=(1+1/s)^n-1$. At $s=\rho-1$,

$$
\operatorname{Res}\left[k_n(s)\left(-\frac{\zeta'}\zeta(1+s)\right)
\right]
=-m_\rho k_n(\rho-1)
=m_\rho\left[1-\left(\frac\rho{\rho-1}\right)^n\right].
$$

Reflection $\rho\mapsto1-\rho$ preserves the full ordinate cutoff,
so these nontrivial-zero residues sum to $+L_n(T)$. The unnumbered
contour expansion following (6.5) instead inserts $+k_n(\rho-1)$;
its subsequent (6.7), printed p.1723, has $-L_n(T)$.
Definitions (1.1), (4.5)--(4.8) and (6.1) supply no compensating
convention change in the classical zeta specialization. A local
sign repair would reverse this contribution. It alone would not
establish the remaining contour estimates, and no corrected version
of the signed asymptotic is asserted here.

There is also an independent weak-tail consistency check. Pair
$\rho=\beta+i\gamma$ with its conjugate and put $z=1-1/\rho$.
For $\gamma>\sqrt n$, $0<\beta<1$ gives
$|z|\le1+1/(2\gamma^2)$ and $\Re(1/\rho)=O(\gamma^{-2})$.
Taylor's formula for the polynomial $z^n$ at one gives

$$
|z^n-1-n(z-1)|
\le\tfrac12n(n-1)|z-1|^2\max(1,|z|)^{n-2},
$$

so the complete conjugate pair satisfies
$|(1-z^n)+(1-\bar z^n)|\ll n^2/\gamma^2$ uniformly in this
range. Reusing $N(T)=O(T\log T)$, including multiplicities, gives
$\sum_{\gamma>T}m_\rho\gamma^{-2}=O(\log T/T)$ and hence

$$
\lambda_n-L_n(\sqrt n)=O(n^{3/2}\log n).
\tag{ST1}
$$

The paired tail is absolutely convergent for each fixed $n$, so it
also agrees with the ordinate-cutoff convention for the complete
Li sum. Combining ST1 with the exact classical split from published
Lemma 4.4, $\lambda_n=S_\infty(n)-S_f(n)+1$, shows that **if** the
literal plus-sign approximation (6.2) were used, it would imply

$$
2\lambda_n=S_\infty(n)+1+O(n^{3/2}\log n).
$$

Published Theorem 5.1 supplies $S_\infty(n)=O(n\log n)$
unconditionally. The displayed implication would therefore give
polynomial absolute growth and RH by the existing all-index criterion.
It is an implication from a sign-sensitive premise, not an acquired
bound: we do not import that premise pending clarification of its proof.
No conclusion that the printed statement is false, new literature
priority, Lean certification, or RH proof follows. The generating-function
identity and the Fibonacci growth derivation above use neither (6.2)
nor its contested zero-residue sign.

## A one-sided Li tail bound from reciprocal zero pairing

The original joint matrix is the $(G_b,G_c)$ specialization of
[published Theorem 3.1, equation (3.3)](https://aif.centre-mersenne.org/item/10.5802/aif.2311.pdf),
printed p.1705, where $G_n(s)=1-(1-1/s)^n$. Its entries are
$\lambda_n+\lambda_{-m}-\lambda_{n-m}$; zeta reflection gives
$\lambda_{-m}=\lambda_m$. This existing joint identity is used directly.

This is a paper application of the classical Li zero sum, the functional
equation and the unit-circle Gram identity already used in the
[generalized Li interface](freitas2006li.md). The explicit fourth-moment
allowance is reused from
[VH5--VH6](../Weil/fukushima2011dirichlet.md#reuse-the-inclusive-verified-head-and-the-strict-actual-zero-tail).
No corrected version of the sign-sensitive contour formula (6.2) is
assumed. The application estimates the actual tail's possible negative
contribution; it supplies no sign for the complete Li matrix, Robin or RH.
It has no new Lean certification or literature-priority claim.

Let $a,b$ be positive integers and $c=a+b$. For an integer $H\ge5$ put

$$
\lambda_n^{\rm head}(H)=
\sum_{|\Im\rho|\le H}m_\rho
 \left[1-\left(1-\frac1\rho\right)^n\right],
\qquad
\lambda_n^{\rm tail}(H)=\lambda_n-\lambda_n^{\rm head}(H).
$$

The sum is over distinct nontrivial zeros, with their full analytic
multiplicities. Zeros at height exactly $H$ stay in the head. Use the
original linear matrix map

$$
\mathcal M(x_a,x_b,x_c)=
\begin{pmatrix}
2x_b&x_b+x_c-x_a\\
x_b+x_c-x_a&2x_c
\end{pmatrix},
\qquad K^{\rm tail}_{a,b}(H)=
\mathcal M(\lambda_a^{\rm tail},\lambda_b^{\rm tail},
           \lambda_c^{\rm tail}).
$$

Write $S_4^+(H)=\sum_{\Im\rho>H}m_\rho/(\Im\rho)^4$.
The existing allowance, for $L_H=\lfloor\log_2(H+4)\rfloor+1$, is

$$
\begin{aligned}
\mathscr R_4(H)&=\frac{256}{H}
\left[\left(\frac2{H^3}+\frac1{2H^2}\right)L_H+
\frac{2/H^2+1/H}{H+4}\right],\\
S_4^+(H)&\le\tfrac12\mathscr R_4(H).
\end{aligned}
\tag{RT1}
$$

The factor $1/2$ uses conjugation: VH6 already counts both ordinate signs.
Its supplier is `finite_inverse_fourth_tail_le`, applied to the actual
ordinate and multiplicity with $A=128$, $T=H$, $L=L_H$, and
`zeroData_large_window_count`, then to the supremum of finite subsets.
No spectral-ball containment or newly verified zero height is required.

### Keep each reflected pair's common phase

For an upper zero $\rho=\beta+i\gamma$, $\gamma>H$, set

$$
z_\rho=1-\frac1\rho=e^{d_\rho}w_\rho,
\qquad |w_\rho|=1,\quad d_\rho=\log|z_\rho|.
$$

The strip $0<\beta<1$ gives

$$
|d_\rho|=
\frac12\left|\log\frac{\gamma^2+(1-\beta)^2}{\gamma^2+\beta^2}\right|
\le\frac1{2\gamma^2}.
$$

Indeed the logarithm is $1/\gamma^2$-Lipschitz on the two positive
arguments and their distance is $|1-2\beta|\le1$.
The functional equation and conjugation preserve multiplicities and the
upper tail under $\rho\mapsto1-\overline\rho$. They give exactly

$$
z_{1-\overline\rho}=\frac1{\overline{z_\rho}},\qquad
 d_{1-\overline\rho}=-d_\rho,\qquad
 w_{1-\overline\rho}=w_\rho.
$$

Define the comparison coefficients on these same upper zeros by

$$
C_n(H)=2\sum_{\Im\rho>H}m_\rho(1-\Re w_\rho^n).
$$

They converge for each fixed $n$: $|w_\rho-1|\le2/\gamma$,
$2(1-\Re w_\rho^n)=|1-w_\rho^n|^2\le4n^2/\gamma^2$, and the
classical reciprocal-square zero tail is summable.
On every finite interval $H<\gamma\le Y$, average over the reflected
permutation before taking $Y\to\infty$. The exact difference is

$$
\Delta_n(H):=\lambda_n^{\rm tail}(H)-C_n(H)
=-2\sum_{\Im\rho>H}m_\rho
       (\cosh(nd_\rho)-1)\Re w_\rho^n.
$$

Thus the first radial variation cancels on the actual reflected zero
set. From $\cosh x-1\le x^2e^{|x|}/2$, for $1\le n\le c$,

$$
|\Delta_n(H)|\le
\frac{n^2}{4}e^{c/(2H^2)}S_4^+(H)
\le\frac{n^2}{8}e^{c/(2H^2)}\mathscr R_4(H).
\tag{RT2}
$$

The error series is absolutely convergent. This argument reorders no
unpaired infinite zero sum and discards no off-line partner.

### The original mixed entry survives the comparison

For each upper zero the matrix
$\mathcal M(2(1-\Re w^a),2(1-\Re w^b),2(1-\Re w^c))$
is twice the real Gram matrix on $(1-w^b,1-w^c)$, since $c-b=a$.
It is positive semidefinite. The convergent sum therefore gives
$\mathcal M(C_a,C_b,C_c)\succeq0$.
For the error matrix $E=\mathcal M(\Delta_a,\Delta_b,\Delta_c)$,
RT2 and the maximum absolute row sum give

$$
\|E\|_{\rm op}\le
\frac{a^2+b^2+3c^2}{8}e^{c/(2H^2)}\mathscr R_4(H)
\le\frac{c^2}{2}e^{c/(2H^2)}\mathscr R_4(H)
=:\eta_c(H).
$$

Consequently the complete actual high-zero matrix satisfies

$$
\boxed{K^{\rm tail}_{a,b}(H)\succeq-\eta_c(H)I_2.}
\tag{RT3}
$$

The two scalar directions needed by
[CS29](coffey2009stieltjes.md#cs10-two-weaker-signed-targets-on-the-actual-middle)
also follow directly, with

$$
\begin{aligned}
\lambda_c^{\rm tail}(H)&\ge
-\frac{c^2}{8}e^{c/(2H^2)}\mathscr R_4(H),\\
2\lambda_a^{\rm tail}(H)+2\lambda_b^{\rm tail}(H)
 -\lambda_c^{\rm tail}(H)&\ge
-\frac{2a^2+2b^2+c^2}{8}e^{c/(2H^2)}\mathscr R_4(H).
\end{aligned}
\tag{RT4}
$$

For the second inequality the comparison direction is nonnegative
because it equals $(2,-1)\mathcal M(C_a,C_b,C_c)(2,-1)^{\mathsf T}/2$.
The same zeros, phases and cutoff occur in both directions.

### A sublinear negative allowance, with the unknown head retained

For $c\ge25$ take the single symbolic choice
$H_c=\lceil\sqrt c\rceil$. Since
$\mathscr R_4(H)=O(\log H/H^3)$ and $c/H_c^2\le1$,

$$
\eta_c(H_c)=O(\sqrt c\log c)=o(c),\qquad
K_{a,b}\succeq K^{\rm head}_{a,b}(H_c)-\eta_c(H_c)I_2.
\tag{RT5}
$$

No zero computation, height scan or change to an arithmetic cutoff is
used. At adjacent Fibonacci indices,
[CS28](coffey2009stieltjes.md#cs9-a-classical-bound-pays-the-growing-low-prime-prefix)
already gives the original
actual arithmetic middle, with the complete $h^*=H+U-B$, all prime powers
and its original endpoints. If its stated allowance is
$\epsilon_{\rm mid}(c)=o(c)$, then

$$
\boxed{K_j^{\rm mid}\succeq
K_j^{\rm head}(H_c)-
 [\eta_c(H_c)+\epsilon_{\rm mid}(c)]I_2.}
\tag{RT6}
$$

RT3 is a lower bound, not an operator-norm bound on the tail itself.
The head in RT5--RT6 contains every actual zero through the growing
height $H_c$, including unverified off-line zeros and their
multiplicities; no positivity or polynomial lower bound for that head
has been acquired. With a fixed verified height instead, the allowance
retains its factor $e^{c/(2H^2)}$ and supplies no cofinal polynomial
budget. The original head probes, CS29, Robin and RH remain unresolved.
