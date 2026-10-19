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

## The actual high-zero Fibonacci block carries a positive budget

Keep RT1--RT6's actual zeta zero sums, their original two-coordinate matrix
$\mathcal M$, all multiplicities and the inclusive head convention.
Let $a\le b$ be adjacent positive Fibonacci numbers and $c=a+b\ge1024$.
Use the single cutoff $H=c$: the head contains $|\Im\rho|\le c$ and
the tail contains $|\Im\rho|>c$. Put
$$
 S_4^+(c)=\sum_{\Im\rho>c}\frac{m_\rho}{(\Im\rho)^4}.
$$
This is the same convergent positive zero tail used in RT1.
The added estimate is an actual positive lower bound for this complete
tail, rather than another estimate for the unitary-comparison error:
$$
 \boxed{\quad K^{\rm tail}_{a,b}(c)
       \succeq \frac{c^4}{2^{19}}S_4^+(c)\,I_2\succ0.\quad}
 \tag{PTL1}
$$
It uses the existing reflected-pair identity and unit-circle Gram matrix.
The classical zero-counting asymptotic below is reused, not reproved.
This is a paper application without new Lean certification or a
literature-priority claim; it supplies no sign for the unknown head.

### Retain a uniformly positive Gram determinant

For the SAME upper zero $\rho=\beta+i\gamma$, $\gamma>c$, write
$1-1/\rho=e^{d_\rho+i\theta_\rho}$ as in RT2. The open critical strip gives
$$
 \theta_\rho=
 \arctan\frac{\beta}{\gamma}
 +\arctan\frac{1-\beta}{\gamma},\qquad
 \frac1{2\gamma}\le\theta_\rho\le\frac1\gamma,\qquad
 |d_\rho|\le\frac1{2\gamma^2}.
 \tag{PTL2}
$$
The angle bounds use
$x/(1+x^2)\le\arctan x\le x$ for $x\ge0$.
In particular $0<c\theta_\rho<1$.

Set $A=a\theta_\rho/2$, $B=b\theta_\rho/2$ and
$C=c\theta_\rho/2$, so $C-B=A$. The unit-circle comparison matrix
for the coefficient triple $2(1-\cos(n\theta_\rho))$ is exactly
$$
 G_\rho=
 8\begin{pmatrix}
 \sin^2B&\sin B\sin C\cos A\\
 \sin B\sin C\cos A&\sin^2C
 \end{pmatrix}.
$$
All three angles lie in $(0,1/2)$. Thus
$$
 \det G_\rho=64\sin^2A\sin^2B\sin^2C>0,\qquad
 \operatorname{tr}G_\rho=8(\sin^2B+\sin^2C).
$$
Using $\sin x\ge x/2$ on $[0,1/2]$, $\sin x\le x$, and
$\lambda_{\min}\ge\det/\operatorname{tr}$ for a positive $2$-by-$2$
matrix gives
$$
 \lambda_{\min}(G_\rho)
 \ge \frac{a^2b^2c^2\theta_\rho^4}{128(b^2+c^2)}
 \ge \frac{a^2b^2c^2}{2048(b^2+c^2)\gamma^4}
 \ge \frac{c^4}{147456\gamma^4}
 \ge \frac{c^4}{2^{18}\gamma^4}.
 \tag{PTL3}
$$
Here adjacency gives $a\ge c/3$, $b\ge c/2$ and
$b^2+c^2\le2c^2$. No phase independence or verification that this
zero lies on the critical line is assumed.

### Pay the radial error on the same reflected pair

Reflection of the upper zero, $\rho\mapsto1-\bar\rho$, preserves
the ordinate and multiplicity, preserves $\theta_\rho$ and changes
$d_\rho$ to $-d_\rho$. RT2 therefore represents the complete tail by
summing the matrices from the reflected-average coefficient triple
$$
 T_n(\rho)=2\bigl(1-\cosh(nd_\rho)\cos(n\theta_\rho)\bigr),
 \qquad n=a,b,c.
$$
This is an equality AFTER reflection averaging over the actual
upper-zero set; it does not replace each unaveraged zero response
by an independently chosen phase.

For $1\le n\le c$, the existing radial-error estimate gives
$$
 |T_n(\rho)-2(1-\cos(n\theta_\rho))|
 \le n^2d_\rho^2e^{c|d_\rho|}
 \le \frac{n^2}{4\gamma^4}e^{c/(2\gamma^2)}.
$$
Write $E_\rho=\mathcal M(T_a,T_b,T_c)-G_\rho$.
The original matrix map and its maximum absolute row sum give
$$
 \|E_\rho\|_{\rm op}
 \le\frac{a^2+b^2+3c^2}{4\gamma^4}
          e^{c/(2\gamma^2)}
 \le\frac{2c^2}{\gamma^4}
 \le\frac{c^4}{2^{19}\gamma^4}.
$$
The last inequality uses $c\ge1024$; the exponential is at most two
because $\gamma>c$. Combining this with PTL3 yields
$$
 \mathcal M(T_a(\rho),T_b(\rho),T_c(\rho))
       \succeq\frac{c^4}{2^{19}\gamma^4}I_2.
 \tag{PTL4}
$$
Sum first over $c<\gamma\le Y$, where the reflected permutation is
exact, and then let $Y\to\infty$ using RT2--RT3's convergence.
All upper-zero multiplicities remain in this sum. This proves PTL1.
Strict positivity uses the classical infinitude of zeta zeros and
$S_4^+(c)>0$.

### Use the positive tail on the original arithmetic middle

Let $N_+(T)$ count the actual upper zeros with $0<\Im\rho\le T$,
with analytic multiplicity. The same tail and its contained annulus give
$$
 \frac{c^4}{2^{19}}S_4^+(c)
 \ge\frac{N_+(2c)-N_+(c)}{2^{23}}.
$$
Reuse Lagarias, [arXiv:math/0404394v4](https://arxiv.org/html/math/0404394),
Theorem 2.1(4), equations (2.29)--(2.30), specialized to the trivial
representation ($N=1$, conductor $Q=1$). This is the unconditional
Riemann--von Mangoldt formula in the upper-zero convention:
$$
 N_+(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}
           -\frac{T}{2\pi}+O(\log T).
$$
It follows that
$$
 \frac{N_+(2c)-N_+(c)}{2^{23}}
 =\left(\frac1{2^{24}\pi}+o(1)\right)c\log c.
 \tag{PTL5}
$$
The source's strict upper endpoint can be changed to this inclusive
convention: its formula bounds a jump's multiplicity by $O(\log T)$,
so the same error term remains valid. Zeros at $c$ remain in the head;
zeros at $2c$ stay in this annulus. No ordinate scan, zero certification
or RH premise is used.

For the SAME $K_j^{\rm mid}$ and original arithmetic endpoints in
CS28, retain its actual common-matrix approximation allowance
$\epsilon_{\rm mid}(c)=o(c)$. PTL1 gives
$$
 \boxed{\quad
 K_j^{\rm mid}\succeq K_j^{\rm head}(c)
 +\left[\frac{c^4}{2^{19}}S_4^+(c)
            -\epsilon_{\rm mid}(c)\right]I_2.
 \quad} \tag{PTL6}
$$
Consequently every fixed $\kappa<1/(2^{24}\pi)$ gives
$K_j^{\rm mid}\succeq K_j^{\rm head}(c)+\kappa c\log c\,I_2$
for all sufficiently large adjacent Fibonacci triples.

The head at this cutoff contains all actual zeros through height $c$,
including any unverified off-line zeros and their multiplicities.
Its lower bound remains unknown. PTL6 would pay a negative head
of size smaller than the displayed positive budget, but does not
establish such a head bound. Compared with RT5--RT6's head at
$\lceil\sqrt c\rceil$, this is a different decomposition of the SAME
full matrix; no order comparison of the two heads is asserted.
No positivity of the complete Li matrix, full retained Schur minimum,
all-integer Robin, endpoint half-variance target or RH follows.

## Reuse the joint zero sum to reduce the unpaid Li head

Keep the actual Fibonacci matrix, all zero multiplicities and the
inclusive-head convention of RT1--RT6 and PTL1--PTL6. Put
$$
 L=\log c,\qquad
 \Omega_c=(L/\log L)^{1/3},\qquad
 h_c=\left\lceil\sqrt{\frac{c}{2L}}\right\rceil,\qquad
 R=57.54,\qquad \nu=\frac1{20R}.
$$
Work for sufficiently large adjacent positive Fibonacci $a\le b$,
$a+b=c$, so $h_c\ge3\cdot10^{12}$ and $h_c<c$.
No numerical starting value of $c$ is certified.

For every integer cutoff $h_c\le H\le c$, the complete actual tail has
$$
 \boxed{\quad
 K^{\rm tail}_{a,b}(H)
 \succeq[\mu_c-\mathscr E_c]I_2,\qquad
 \mu_c=\frac{c^4}{2^{19}}S_4^+(c),\qquad
 \mathscr E_c\ll c e^{-\nu\Omega_c}=o(c).
 \quad} \tag{DHR1}
$$
Thus every fixed $0<\kappa<1/(2^{24}\pi)$ gives
$K^{\rm tail}_{a,b}(H)\succeq\kappa c\log c\,I_2$ eventually,
uniformly over these cutoffs. The smaller exact head still grows
without bound. This is a paper application of an owned zero-sum
bound, without new Lean certification or a literature-priority claim.

### Use the existing weighted sum at an auxiliary parameter

The [joint density and zero-free application](../ArithSums/nicolas2025comparison.md#a-smaller-moving-cut-from-joint-density-and-zero-free-support)
already bounds the intermediate positive quantity
$$
 B_2(A;T)=\sum_{\gamma>T}
 \frac{m_\rho\bigl(A^{\beta-1/2}+A^{1/2-\beta}\bigr)}{\gamma^2}.
$$
For $\ell=\log A$, $\Omega(A)=(\ell/\log\ell)^{1/3}$ and
$T_A=A^{1/4}e^{-\Omega(A)/(28R)}$, its bound is
$$
 B_2(A;T_A)\ll
 \ell A^{-1/8}e^{\Omega(A)/(28R)}
 +\ell^3e^{-\Omega(A)/(14R)}
 +\ell^3A^{-1/14}.
 \tag{DHR2}
$$
This intermediate estimate uses the positive real parameter $A$
and the actual upper-zero multiset; no source-selection property
of $A$ enters its proof. Here $A_c=c^2$ is an auxiliary parameter.

The uniform explicit Ingham input and Ford zero-free support in
that application are reused as stated there. Their analytic
proofs and finite verified-height input remain external premises;
global RH is not a premise. No density-layer proof or zero
computation is repeated for the Li consumer.

### Dominate the Li radial charge pointwise

For the SAME upper zero put $\delta_\rho=|\beta-1/2|$.
RT2's logarithmic calculation gives
$|d_\rho|\le\delta_\rho/\gamma^2$.
After its multiplicity-preserving reflection average, the index
$n\le c$ error is at most $n^2d_\rho^2e^{c|d_\rho|}$.
The original mixed entry and its row sum therefore give the
nonnegative allowance
$$
 \mathscr E_c:=
 4c^2\sum_{\gamma>h_c}
 \frac{m_\rho\delta_\rho^2}{\gamma^4}
       e^{c\delta_\rho/\gamma^2}.
 \tag{DHR3}
$$
It bounds the unit-phase comparison error on every sub-band of
this tail. Critical-line zeros have zero charge, and the
fourth-moment supplier in RT1 makes the sum finite for fixed $c$.

For $\gamma>h_c$, one has
$c/\gamma^2\le c/h_c^2\le2L$, $4\delta_\rho^2\le1$, and
$$
 e^{c\delta_\rho/\gamma^2}
 \le(c^2)^{\delta_\rho}
 \le(c^2)^{\beta-1/2}+(c^2)^{1/2-\beta}.
$$
Consequently, on the SAME zeros and heights,
$$
 \boxed{\quad
 \mathscr E_c
 \le\frac{c^2}{h_c^2}B_2(c^2;h_c)
 \le2cL\,B_2(c^2;T_{c^2}).
 \quad} \tag{DHR4}
$$
The last inequality uses positivity of the summands and the
eventual comparison
$$
 \frac{h_c}{T_{c^2}}
 \ge\frac{e^{\Omega(c^2)/(28R)}}{\sqrt{2L}}
 \longrightarrow\infty.
$$
This is an upper-bound comparison for one common positive zero
sum. All reflected partners and analytic multiplicities remain.

Substituting $A=c^2$, $\ell=2L$ in DHR2 yields
$$
 \begin{aligned}
 \mathscr E_c\ll{}&
 c^{3/4}L^2e^{\Omega(c^2)/(28R)}
 +cL^4e^{-\Omega(c^2)/(14R)}
 +c^{6/7}L^4\\
 \ll{}&ce^{-\Omega_c/(20R)}=o(c).
 \end{aligned} \tag{DHR5}
$$
Here $\Omega(c^2)/\Omega_c\to2^{1/3}$,
$\Omega_c/\log L\to\infty$ and $\Omega_c=o(L)$.
The first and third terms have a fixed power saving in $c$;
the middle term absorbs the displayed logarithms. No effective
starting clock or new density theorem is claimed.

### Keep the positive budget with the smaller original head

For each $h_c\le H\le c$, use the exact SAME-source decomposition
$$
 K^{\rm tail}_{a,b}(H)
 =K^{\rm tail}_{a,b}(c)+G_{H,c}+E_{H,c},\qquad
 G_{H,c}\succeq0,\qquad
 \|E_{H,c}\|_{\rm op}\le\mathscr E_c.
 \tag{DHR6}
$$
Here $G_{H,c}$ is RT3's unit-phase Gram sum on $H<\gamma\le c$.
Reflection preserves this finite band exactly. PTL1 pays the
complete tail at $c$, and DHR5 pays the whole finite-band error.
This proves DHR1 without subtracting separate lower bounds for
two tails or assuming an order on their heads.

At $H=h_c$, retain CS28's original arithmetic-middle allowance
$\epsilon_{\rm mid}(c)=o(c)$. The original matrix obeys
$$
 \boxed{\quad
 K_j^{\rm mid}\succeq K_j^{\rm head}(h_c)
 +[\mu_c-\mathscr E_c-\epsilon_{\rm mid}(c)]I_2.
 \quad} \tag{DHR7}
$$
The same eventual $\kappa c\log c$ budget is therefore available
with $h_c\sim\sqrt{c/(2\log c)}$ and unchanged arithmetic endpoints.

No lower bound for $K_j^{\rm head}(h_c)$ has been acquired.
It contains every actual zero through $h_c$, including any
unverified off-line zeros; finite verification does not verify
this unbounded head. CS29's original weak signed probes, full
Li/Schur positivity, the same-source Robin strict upper,
strict Robin for every $n>5040$, and RH remain unresolved.

## The complete descended tail has the classical Li main term

Keep DHR1--DHR7's actual zeros, multiplicities, inclusive head and
$h_c=\lceil\sqrt{c/(2\log c)}\rceil$. The radial allowance remains
$\mathscr E_c\ll ce^{-\nu\Omega_c}=o(c)$ with the same external
premises and no effective starting $c$. Let $H_n$ be the already-used
archimedean term from [CS4](coffey2009stieltjes.md#cs4-consumer-the-original-adjacent-fibonacci-joint-matrix):
$$
 H_n=\tfrac n2(\log n+q)+O(1),\qquad
 q=\gamma_{\!E}-1-\log(2\pi).
$$
Here $\gamma_{\!E}$ is Euler's constant, not a zero ordinate.

The complete tail satisfies the two-sided uniform application
$$
 \boxed{\quad
 \max_{1\le n\le c}
 |\lambda_n^{\rm tail}(h_c)-H_n|=o(c).
 \quad} \tag{DLM1}
$$
This uses an existing phase-only asymptotic and the owned actual
radial estimate. It does not use the sign-sensitive contour formula
discussed above or identify the auxiliary phase-only sequence with
the original Li coefficients.

### Reuse the ordinate-sequence theorem

Use Juan Arias de Reyna, *Asymptotics of Keiper-Li coefficients*,
[DOI 10.7169/facm/1317045228](https://doi.org/10.7169/facm/1317045228),
Theorem 1, Section 3, pp.4--5 of the
[author version](https://personal.us.es/arias/56-2RHB.pdf)
dated 31 January 2011. The theorem accepts any nondecreasing positive
sequence, including repetitions, with counting law
$$
 N(t)=\frac{t}{2\pi}\log\frac{t}{2\pi}-\frac{t}{2\pi}+O(\log t).
$$
List the ordinates of ALL actual upper zeros, repeating each according
to its analytic multiplicity. PTL5's existing unconditional count
supplies this hypothesis. Put
$$
 \vartheta_\gamma=2\arctan\frac1{2\gamma},\qquad
 C_n^\circ=2\sum_{\gamma>0}m_\rho
                 [1-\cos(n\vartheta_\gamma)].
$$
The source's $J_n=(4/n)\sum_j\sin^2(n\arctan(1/(2\gamma_j)))$
is exactly $C_n^\circ/n$. Thus its general theorem supplies one fixed
sequence $(y_n)\in\ell^2$ with
$$
 C_n^\circ=\tfrac n2(\log n+q)+ny_n.
 \tag{DLM2}
$$
We use this general ordinate-sequence theorem, not the paper's
RH-conditional identification with actual Keiper coefficients in
Corollary 2. The theorem and its proof are reused as an external
paper-level premise; neither its counting-integral proof nor its
Mellin calculation is repeated here.

### Connect the actual phase and the smaller cutoff

For the SAME actual upper zero put $\delta_\rho=|\beta-1/2|$ and
$w_\rho=e^{i\theta_\rho}$ as in RT2. For $\gamma>h_c\ge5$,
$$
 \theta_\rho=\arctan\frac{\gamma}{\gamma^2-\beta(1-\beta)},\qquad
 0\le\vartheta_\gamma-\theta_\rho
 \le\frac{\delta_\rho^2}{\gamma^3}.
 \tag{DLM3}
$$
Indeed $\vartheta_\gamma$ is the same arctangent at $v=1/4$,
whereas $\theta_\rho$ uses $v=\beta(1-\beta)=1/4-\delta_\rho^2$.
On $0\le v\le1/4$,
$$
 \frac{d}{dv}\arctan\frac{\gamma}{\gamma^2-v}
 =\frac{\gamma}{(\gamma^2-v)^2+\gamma^2}
 \le\gamma^{-3}.
$$
The actual count also gives
$\sum_{\gamma>h}m_\rho\gamma^{-3}=O(\log h/h^2)$.
Comparing the two tail phases therefore costs
$O(c\log h_c/h_c^2)$ uniformly for $n\le c$.
The deleted part of $C_n^\circ$ is at most $4N_+(h_c)$.
DHR3 bounds the actual radial error by $\mathscr E_c/4$ per coefficient.
Together with the owned $H_n$ asymptotic, these give
$$
 \max_{1\le n\le c}
 |\lambda_n^{\rm tail}(h_c)-H_n-ny_n|
 \ll\mathscr E_c+h_c\log h_c+
              c\log h_c/h_c^2+1=o(c).
 \tag{DLM4}
$$
All phase comparisons retain the actual ordinates and multiplicities;
only the auxiliary sequence has its phases projected to the circle.
Every zero at the cutoff stays in the actual head.

Since $y_n\to0$, splitting at any fixed index and then sending that
index to infinity gives
$$
 \frac1c\max_{1\le n\le c}n|y_n|\longrightarrow0.
 \tag{DLM5}
$$
This proves DLM1. No explicit pointwise decay rate for $y_n$, effective
starting clock or new zero verification is asserted.

### Recover the whole matrix shape and isolate the signed low radius

For the original adjacent Fibonacci $a,b,c=a+b$, put $r_c=b/c$ and
$$
 A(r)=\begin{pmatrix}r&r\\r&1\end{pmatrix},\qquad
 B(r)=\begin{pmatrix}
 r(\log r+q)&rq+\tfrac12[r\log r-(1-r)\log(1-r)]\\
 rq+\tfrac12[r\log r-(1-r)\log(1-r)]&q
 \end{pmatrix}.
$$
The original linear map $\mathcal M$ and DLM1 yield, in operator norm,
$$
 \boxed{\quad
 K^{\rm tail}_{a,b}(h_c)
 =c\log c\,A(r_c)+cB(r_c)+o(c).
 \quad} \tag{DLM6}
$$
This is an equality with a norm-small remainder for the ENTIRE
actual tail, rather than an equality asserted for its annulus floor.
Since $r_c\to\varphi^{-1}$, its least eigenvalue satisfies
$$
 \frac{\lambda_{\min}(K^{\rm tail}_{a,b}(h_c))}{c\log c}
 \longrightarrow
 \frac{\varphi-\sqrt{13-7\varphi}}2>0.
 \tag{DLM7}
$$

A finite reflection average also isolates what remains unknown.
Define the actual low-radius defect
$$
 D_n^{\rm low}(h_c)=
 -2\sum_{0<\gamma\le h_c}m_\rho
 [\cosh(nd_\rho)-1]\cos(n\theta_\rho).
$$
Then $\lambda_n^{\rm head}=C_n^{\rm head}+D_n^{\rm low}$ exactly,
where $0\le C_n^{\rm head}\le4N_+(h_c)=o(c)$ uniformly for $n\le c$.
In particular the defect is zero for critical-line zeros; every
actual off-line partner in the low head is still present.
Combining the same exact head with DLM6 and CS28 gives
$$
 \boxed{\quad
 K_j^{\rm mid}=
 \mathcal M(D_a^{\rm low},D_b^{\rm low},D_c^{\rm low})
 +c\log c\,A(r_c)+cB(r_c)+o(c).
 \quad} \tag{DLM8}
$$
No sign or polynomial bound for this finite but growing signed
low-radius defect has been obtained. The original CS29 probes,
complete Li/Schur positivity, strict Robin for every $n>5040$ and RH
remain unproved. No Lean certification, numerical starting value,
new verified height or literature-priority claim is made.

## A finite verified head pays the entire Fibonacci–Li matrix

Keep RT1–RT3 and PTL1–PTL5's actual classical Li coefficients, the
original matrix $\mathcal M$, all analytic multiplicities and the inclusive
head convention. Let $a\le b$ be adjacent positive Fibonacci numbers,
$c=a+b$, and put $H_0=3\cdot10^{12}$. The following is a finite paper
application of those owned estimates and the published suppliers below:

$$
\boxed{K_{a,b}\succ0\quad(1024\le c\le5\cdot10^{25}).}
\tag{FV1}
$$

For the upper part of this interval it supplies a uniform coefficient
bound for the entire matrix:

$$
\boxed{K_{a,b}\succeq10^{-9}c\,I_2
\quad(H_0<c\le5\cdot10^{25}).}
\tag{FV2}
$$

These are statements about every vector in the original two-coordinate
block, including its mixed entry. They do not follow merely from scalar
Li coefficient positivity. They assert no new zero verification, no
literature priority and no Lean certification.

### Published finite inputs

Reuse Platt–Trudgian,
[*The Riemann hypothesis is true up to $3\cdot10^{12}$*,
arXiv:2004.09765v1](https://arxiv.org/pdf/2004.09765v1), Theorem 1,
printed p.2, which verifies through $3000175332800$. Its abstract and
introduction explicitly include $0<\gamma\le H_0$. This is the same
published premise used in the
[verified-height form estimate](../Weil/fukushima2011dirichlet.md#a-sufficient-fixed-gap-supplier-with-its-unpaid-inputs).
No computation underlying that premise is repeated.

For an explicit zero-count input reuse Hasanalizade–Shen–Wong,
[*Counting zeros of the Riemann zeta function*,
arXiv:2107.06506v1](https://arxiv.org/pdf/2107.06506v1), Corollary 1.2,
printed p.2, equation (1.5). For $T\ge e$ it states

$$
|N_+(T)-N_0(T)|
\le0.1038\log T+0.2573\log\log T+9.3675,
\qquad N_0(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}.
$$

The introduction defines $N_+$ with $0<\gamma\le T$; its argument-principle
count in §2 includes analytic multiplicity. At a zero ordinate the same
inclusive convention is obtained by approaching from above. The
source's proof and numerical choices are not replayed. This is the
zero-count supplier already used in the
[finite Robin tail](../Analytic/polak2026finiterobinca.md#pay-the-entire-range-above-the-second-height).
Since $\log T\ge1$, $\log\log T\le\log T$ and
$0.1038+0.2573+9.3675<10$, it directly gives

$$
|N_+(T)-N_0(T)|\le10\log T\qquad(T\ge e).
\tag{FV3}
$$

Only a coarse substitution into this existing count is needed.

### An explicit positive budget above $c$

For $c>H_0$ write $L=\log c>24$. Indeed $e<3$ and $3^4<100$ give
$e^{24}<10^{12}<H_0$. From $\pi<4$, $\log(2/\pi)>-1$, and FV3,

$$
\begin{aligned}
N_+(2c)-N_+(c)
&\ge\frac{c}{2\pi}\bigl[L+\log(2/\pi)-1\bigr]
 -10\log(2c)-10\log c\\
&>\frac{c}{8}(L-2)-30L\\
&>\left(\frac{11c}{96}-30\right)L
\ge\frac{cL}{16}.
\end{aligned}
\tag{FV4}
$$

The last inequality uses $c\ge576$. PTL1 and its same-tail annulus
bound PTL5 therefore give

$$
K^{\rm tail}_{a,b}(c)\succeq\mu_c I_2,
\qquad \mu_c=\frac{c^4}{2^{19}}S_4^+(c)
\ge\frac{N_+(2c)-N_+(c)}{2^{23}}
>\frac{3c}{2^{24}}.
\tag{FV5}
$$

The complete actual tail above $c$ remains in the block; no annulus
replaces it by equality.

### The intervening band retains its common Gram part

If $1024\le c\le H_0$, the actual head through $c$ lies on the critical
line by the published verification and is a positive semidefinite Gram
sum. PTL1 makes its complete tail strictly positive, proving FV1 in
this range.

Now suppose $H_0<c\le5\cdot10^{25}$. Apply RT2–RT3's reflected comparison
only on the finite band $H_0<\gamma\le c$. Reflection preserves this
band and every multiplicity. Its unit-phase matrix $G_{H_0,c}$ is
positive semidefinite; its error $E_{H_0,c}$ obeys RT3's row bound with
the larger positive full tail $S_4^+(H_0)$ as envelope. Thus exactly

$$
\begin{aligned}
K_{a,b}&=K^{\rm head}_{a,b}(H_0)+G_{H_0,c}+E_{H_0,c}
 +K^{\rm tail}_{a,b}(c),\\
K^{\rm head}_{a,b}(H_0)&\succeq0,\qquad G_{H_0,c}\succeq0,\\
\|E_{H_0,c}\|_{\rm op}
&\le\frac{c^2}{2}e^{c/(2H_0^2)}\mathscr R_4(H_0).
\end{aligned}
\tag{FV6}
$$

These four contributions partition the same actual zero sum. In
particular the finite band's Gram part and error are coupled through
the original phases, rather than optimized as independent sources.

At this fixed $H_0$, $L_{H_0}=42$ because
$2^{41}<H_0+4<2^{42}$. The owned RT1 formula gives, using
$(2/H_0^2+1/H_0)/(H_0+4)<H_0^{-2}$,

$$
\mathscr R_4(H_0)
<\frac{5632}{H_0^3}+\frac{21504}{H_0^4}
<\frac{5633}{H_0^3}<\frac1{4\cdot10^{33}}.
\tag{FV7}
$$

Here $H_0>21504$ and the final rational comparison is $22532<27000$.
Moreover $c/(2H_0^2)\le25/9<3$ and $e^3<27$. Hence

$$
\|E_{H_0,c}\|_{\rm op}
<\frac{27c^2}{8\cdot10^{33}}
\le\frac{135c}{8\cdot10^8}.
\tag{FV8}
$$

Combining FV5–FV8 on this same block yields

$$
K_{a,b}\succeq
c\left(\frac3{2^{24}}-\frac{135}{8\cdot10^8}\right)I_2
\succeq10^{-9}c\,I_2.
\tag{FV9}
$$

For the final outward comparison, $2^{24}=16777216<17000000$ gives
$3/2^{24}>7/(4\cdot10^7)$; the bracket exceeds
$5/(8\cdot10^8)>10^{-9}$. This proves FV2 and the rest of FV1.
All constant comparisons here are elementary paper inequalities; no
zero scan, Li-coefficient evaluation or new experiment is used.

### The unbounded head remains the missing input

This finite result retains every actual zero and controls every direction
of the original block. It is not an effective claim about the original
arithmetic middle: CS28 supplies an $o(c)$ transfer without a certified
finite common starting value, so that transfer cannot be substituted
into FV1–FV2 over the displayed interval. The finite block bound supplies
neither a Robin interval for all integers nor a cofinal signed head bound.
The full RH and strict Robin for every integer $n>5040$ remain unresolved.

## An effective Fibonacci observation window and its original signed consumer

This paper application uses FG2--FG8, CS29 and the explicit whole-matrix
transfer EB1--EB5. The chain and membership input is Grzegorz Pastuszak, *On ascending chains of ideals in the
polynomial ring*, arXiv:1605.06263v1, Theorem 3.5, Theorem 4.2 and Corollary 4.5,
PDF pp.9--13, https://arxiv.org/html/1605.06263v1 .
The generic chain and membership proofs are not repeated. The journal article
is *Ascending chains of ideals in the polynomial ring*, Turkish J. Math. 44
(2020), 2402--2414, DOI 10.3906/mat-1904-61; formula locations here use v1.

Write $\mathcal B(n,f)$ for the explicit integer recursion in that source's
Theorem 3.5 (Proposition 3.1 and Corollary 3.4). It bounds the number of ideals
in a strict chain whose $r$-th ideal has generators of total degree at most
the nondecreasing integer function $f(r)$. No unspecified constant is
included in this notation. The source's Corollary 4.5 also bounds the degrees
in an ordinary ideal-membership certificate over any field; it is not
radical membership.

### EO1. A fixed polynomial carrier bounds the window

Use FG2's $d\ge1$, positive integers $m_i$, $M=\sum_i m_i$, Laurent
automorphism $\sigma X_i=Y_i,\ \sigma Y_i=X_iY_i$, and
$p=\sum_i m_iX_i$. Set
$$
 n=4d,\quad f(r)=2^{r+1}\ (r\ge1),\quad K=\mathcal B(n,f),\quad D=2^{K+1}.
 \tag{EO1}
$$
In $\mathbb Q[X,Y,U,V]$, impose
$$
 \mathfrak a=(X_iU_i-1,Y_iV_i-1:1\le i\le d).
$$
The quotient is exactly the original Laurent ring, by $U_i=X_i^{-1}$,
$V_i=Y_i^{-1}$. For $r\ge1$ the forward polynomial lift is
$$
 p_r=\sum_i m_iX_i^{F_{r-1}}Y_i^{F_r}.
$$
Its degree is $F_{r+1}\le2^r$. Put
$J_r=\mathfrak a+(p_1,\ldots,p_r)$. Its displayed generators have degree
at most $f(r)$. Pastuszak's chain bound forces $J_s=J_{s+1}$ for some
$1\le s\le K$: otherwise $J_1,\ldots,J_{K+1}$ would be a longer strict
chain. In the Laurent quotient, $\sigma\overline J_s\subseteq\overline J_s$.
The same automorphism/Noetherian invariance argument already used in FG2
gives equality, so $p=\sigma^{-1}p_1\in\overline J_s$.
Since every $J_s$ contains the quotient kernel, this gives the ORDINARY
polynomial membership
$$
 p\in J_s\subseteq J_K.
 \tag{EO2}
$$
There is no localization saturation left to assume and no power of $p$
is substituted for $p$.

### EO2. A finite coefficient system bounds the certificate norm

Let $g_D(r)=3^rD$ for $r\ge1$, and define the integers
$$
 T=D\,3^{\mathcal B(n,g_D)}+1,\qquad
 N=\binom{n+T+D}{n},\qquad
 C=N\,N!\,M^N.
 \tag{EO3}
$$
Pastuszak's Corollary 4.5 bounds the membership coefficients by
$(3^{\mathcal B(n,g_D)-1}-1)D+1\le T$.
Apply it to EO2 and the $K+2d$ displayed generators, all of degree at most
$D$. Equating coefficients up to degree $T+D$ is a consistent finite
linear system over $\mathbb Q$, with at most $N$ rows. All entries,
including the right-hand side, are integers of absolute value at most $M$.

For clarity, the needed norm bound is the finite parameter calculation:
choose independent columns spanning the target and independent rows of
their rank $r$, $1\le r\le N$. Set the other unknown coefficients to zero.
Cramer's rule on the resulting nonsingular integer minor gives at most
$r$ nonzero rational coefficients, each bounded by $r!M^r$, since the
nonzero integer denominator has absolute value at least one. Thus the total
coefficient 1-norm is at most $N\,N!\,M^N=C$. Substitution of the inverse
variables cannot increase that norm; the $\mathfrak a$-terms vanish.
Consequently the original Laurent ring has the certificate
$$
 p=\sum_{r=1}^K a_r\sigma^rp,\qquad
 \sum_{r=1}^K\|a_r\|_1\le C.
 \tag{EO4}
$$
Both $K$ and $C$ are specified integer functions of $d,m_i$.
No phase algebraicity, phase separation, generic position or new
Groebner computation is required.

FG3 therefore applies directly with these $K,C$:
$$
 \max_{0\le r<K}\left|\sum_i m_i u_i^{F_{j+r}}\right|
 \ge M C^{-j}\qquad(j\ge0,\ |u_i|=1).
 \tag{EO5}
$$
This is the existing observation inequality with a paid quantitative
interface, not a reproof of its dynamics or a new growth criterion.

### EO3. Retain the actual Li poles and their whole analytic remainder

Suppose the actual Li generating function has nearest poles as in FG6--FG8.
Use ALL nearest poles and their multiplicities, put $R=|z_i|>1$, and
choose the same $r_0<r_1<1$ isolating that complete packet. Set
$$
 B=1/r_1,\quad 1<B<R,\quad
 A=\max\left(1,\sup_{|w|=r_1}|H(w)|\right).
$$
Here $H$ is exactly FG8's pole-subtracted actual generating function.
The existing Cauchy estimate at this radius reads
$$
 \lambda_n=-\sum_i m_i z_i^n+E_n,\qquad |E_n|\le AB^n
 \quad\hbox{for every }n\ge1.
 \tag{EO6}
$$
These are actual, potentially unknown spectral/envelope parameters; a
certified numerical horizon would require bounds for them. They are not
supplied by finite RH verification or postulated from a substitute model.

EO5 and EO6 give, for every integer $j\ge1$, in the block
$j,\ldots,j+K-1$, some $\ell$ with
$$
 |\lambda_{F_\ell}|
 \ge R^{F_\ell}MC^{-j}-AB^{F_\ell}.
 \tag{EO7}
$$
This directly consumes the effective constants on the same original
coefficients.

### EO4. A finite violation of the unchanged arithmetic-middle probes

For every triple $a=F_{k-2},b=F_{k-1},c=F_k$, keep exactly CS28/EB's
$X_c=\lceil\exp(c^4)\rceil$, full $h^*$, powers and endpoints. Write
$$
 P_k=\lambda_c^{\rm mid}(c),\qquad
 Q_k=2\lambda_a^{\rm mid}(c)+2\lambda_b^{\rm mid}(c)
          -\lambda_c^{\rm mid}(c).
$$
Fix any probe allowance $C_0\ge0$. Define
$$
 W=\max\{1,3(C_0+1),(M+A)R^{F_{199}}\},
$$
$$
 \delta=\min\{\log(R/B),\log R,1\}>0,\quad
 L_*=\log C+3\log2+1,
$$
$$
 H_*=1+\log^+(2A/M)+\log^+(2W/M)+3K\log2,
$$
$$
 q=200+\left\lceil8(L_*+H_*+1)/\delta\right\rceil,\qquad j_*=2q+2.
 \tag{EO8}
$$
Here $\log^+x=\max(0,\log x)$. Then there is an index
$$
 200\le k\le j_*+K-1
 \quad\hbox{such that}\quad
 P_k<-C_0F_k^2\ \ \hbox{or}\ \ Q_k<-C_0F_k^2.
 \tag{EO9}
$$

To verify the finite consumer, suppose both inequalities fail to be strict
violations for all those $k$. Put
$\epsilon(c)=1000c^{3/4}(\log c)^{-3/4}+5$.
The owned EB whole-matrix bound gives an error at most $\epsilon/2$
in $P_k$. The linear functional for $Q_k$ on the matrix is
$2K_{11}-2K_{12}+K_{22}/2$; its coefficient matrix is positive rank one
with trace $5/2$, so its error is at most $5\epsilon/2$.
For all $k\ge200$, $F_{k-2}\ge F_{198}\ge2^{98}>10^{24}$;
EB's bound $\epsilon<c/16000+5$ in particular pays both errors by $c^2$.

The SAME actual coefficients consequently satisfy, on this finite range,
$$
 \lambda_c\ge-(C_0+1)c^2,\qquad
 |\lambda_c|\le2|\lambda_a|+2|\lambda_b|+(C_0+1)c^2.
$$
The actual seeds at indices 198 and 199 are bounded by $W F_i^3$, by
EO6 and $1<B<R$. CS29's existing finite induction therefore gives
$$
 |\lambda_{F_i}|\le WF_i^3\qquad(198\le i\le j_*+K-1).
 \tag{EO10}
$$
Its exact cubic contraction $2a^3+2b^3\le2c^3/3$ is reused.

On the other hand, $F_{j_*}\ge2^q$, $2^q\ge q^2$ for $q\ge4$, and
the choice in EO8 gives
$$
 \delta F_{j_*}>j_*L_*+H_*.
$$
Using $F_{j_*+K-1}\le2^{j_*+K-2}$, this implies both
$$
 F_{j_*}\log(R/B)>j_*\log C+\log(2A/M),
$$
$$
 F_{j_*}\log R>
 j_*\log C+\log(2W/M)+3\log F_{j_*+K-1}.
$$
EO7 supplies an $\ell\in[j_*,j_*+K-1]$ with
$$
 |\lambda_{F_\ell}|
 \ge \tfrac M2 C^{-j_*}R^{F_\ell}
 >W F_{j_*+K-1}^{\,3}\ge W F_\ell^3,
$$
contradicting EO10. This proves EO9 with the complete actual arithmetic
middle and no discarded zero or endpoint.

The result is a data-dependent finite signed-witness estimate under the
actual off-line-pole hypothesis. It supplies neither those hypothetical
pole data nor an unconditional lower bound on the original probes. There
is no universal finite RH test, new RH equivalent, full Robin interval,
numerical execution, Lean certification or literature-priority claim.
