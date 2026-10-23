---
bibkey: badziahinshallit2023kronecker
authors: Dmitry Badziahin; Jeffrey Shallit
year: 2023
title: Badly approximable numbers, Kronecker's theorem, and diversity of Sturmian characteristic sequences
doi: 10.5802/jtnb.1236
url: https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.1236/
claim: "The published rotation-gap bound supplies a positive multiplier of at most linear size in the modulus for any fixed golden prefix arc; combined with Gronwall's theorem, every fixed legal Zeckendorf-prefix cylinder has normalized divisor-sum limsup one, without an additive Robin sign or preservation of CA identity."
strata_touched: []
license: citation-only
triage: anchor
---

# Quantitative golden rotation and fixed-prefix Robin saturation

The primary source is Badziahin–Shallit, *Journal de théorie des nombres
de Bordeaux* **35** (2023), no. 1, 1–15,
[DOI:10.5802/jtnb.1236](https://doi.org/10.5802/jtnb.1236).
The [published PDF](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1236.pdf)
has 16 PDF pages including its cover. The definitions on printed pp.2–3,
Theorem 2.3 and Corollary 2.5 were inspected. This is a source-statement
and applicability check, not a complete proof audit or Lean verification.
No source text is vendored.

The application below combines that published bound with the existing
canonical FIB interface and the classical
[Grönwall theorem](../notes/gronwall1913asymptotic.md). It introduces no
new rotation theorem, maximal-order theorem or mathematical originality
claim. A targeted search did not locate a primary publication stating
the complete combined prefix conclusion; that bounded search result
does not establish novelty.

## The published gap supplier

For an irrational real number $\theta$, let $H(\theta,Q)$ denote the
largest circular gap among

$$
\{0,\theta,2\theta,\ldots,Q\theta\}\pmod1,
\qquad Q\in\mathbb N_{>0}.
$$

For an integer $B\ge1$, use $S_B$ here for the irrational members of
the source's set of reals whose continued-fraction partial quotients
after the integer part are at most $B$. The source defines

$$
f(B)=\sup_{\theta\in S_B}\sup_{Q\ge1}QH(\theta,Q).
$$

Theorem 2.3 gives the exact value of $f(B)$; Corollary 2.5 supplies the
bound used here:

$$
H(\theta,Q)\le\frac{f(B)}Q,
\qquad f(B)\le(1+\sqrt{4/5})B<2B
\quad(\theta\in S_B).
\tag{P1}
$$

The parameter $B$ must be supplied for the actual angle. In the application
that angle is $\{m\varphi\}$ and varies with $m$; a fixed bound for the
partial quotients of $\varphi$ alone is insufficient.

## Reuse the exact canonical prefix arc

Set $\varphi=(1+\sqrt5)/2$, $\tau=\varphi^{-1}$, $\psi=-\tau$ and
$F_0=0,F_1=1$. Use canonical digits $\varepsilon_j(n)$ at weights
$F_{j+2}=1,2,3,5,\ldots$, with no adjacent occupied digits.
The unit digit is position zero. The five window labels occupy later
positions and retain their separate unit field and adjacency seams.

The primary digit supplier is Drmota–Müllner–Spiegelhofer,
*Möbius orthogonality for the Zeckendorf sum-of-digits function*,
[arXiv:1706.09680v1](https://arxiv.org/abs/1706.09680v1),
Lemma 1 on PDF p.4, with the preceding interval definition;
the published paper has [DOI:10.1090/proc/14015](https://doi.org/10.1090/proc/14015).
That lemma characterizes fixed low digits by an interval condition on
$(-1)^kn\varphi$ modulo one. Its use is already recorded in the
[FIB theory, §148.2](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
The following parameter correspondence also reuses that volume's
Theorems 116.4–116.5 prefix parameterization; it is not inferred from density.

Let $w=(w_0,\ldots,w_{L-1})$ be a fixed nonempty legal prefix. Put

$$
V=\sum_{j<L}w_jF_{j+2},\quad b=w_{L-1},\quad h=L+b,
\quad a_w=-\sum_{j<L}w_j\psi^{j+2},\quad
J=(-\tau,\tau^2).
$$

Write $C_w$ for the nonnegative integers with that canonical prefix.
The existing shift $s$ gives $C_w=V+s^h(\mathbb N_0)$ and

$$
\eta(n):=n\varphi-s(n)
=-\sum_j\varepsilon_j(n)\psi^{j+2}\in J,
\qquad
\eta(V+s^h(t))=a_w+\psi^h\eta(t).
$$

Equivalently, the primary lemma with $k=L+2$ and $u=V$ supplies
the circular arc

$$
I_w=(a_w+\psi^hJ)\pmod1,\qquad
|I_w|=\varphi^{-h},\qquad
n\in C_w\iff\{n\varphi\}\in I_w\quad(n\ge0).
\tag{P2}
$$

When $b=0$, $V<F_{L+1}$ and the lemma uses its first interval;
when $b=1$, $F_{L+1}\le V<F_{L+2}$ and it uses its second interval.
The latter interval is shorter by one golden scale, matching the
forced zero after the last occupied digit and $h=L+1$.

The two endpoints in (P2), in either order, project to

$$
\{(V-F_{h+1})\varphi\},\qquad
\{(V-F_{h+2})\varphi\}.
$$

Indeed, $\psi^r=F_{r+1}-\varphi F_r$. Legal occupancy gives
$V<F_{h+1}$, so these endpoints are phases of strictly negative
integers. Irrationality prevents any $n\ge0$ from attaining them.
Thus the open-arc convention has no finite-source endpoint exception,
including at $n=0$. Projection to the circle also handles arcs crossing
zero. For $w=(1)$, it gives the existing unit-one interval
$I_w=(2-\varphi,2(2-\varphi))$.
The empty prefix imposes no restriction and needs no arc construction.

## A polynomial-cost multiple in every fixed cylinder

For an integer $r\ge1$, let $a$ be the nearest integer to $r\varphi$.
The nonzero quadratic norm is an integer, so the standard golden
irrational separation estimate follows from

$$
1\le|a^2-ar-r^2|
=|r\varphi-a|\,|r\psi-a|
\le\|r\varphi\|(\sqrt5r+\tfrac12)
<3r\|r\varphi\|.
$$

In particular, for $m,q\ge1$ and $\theta_m=\{m\varphi\}$,

$$
\|q\theta_m\|=\|qm\varphi\|>\frac1{3mq}.
$$

The usual convergent inequality
$\|q_j\theta_m\|<1/(a_{j+1}q_j)$ bounds every partial quotient by
$3m$; this includes the first noninteger quotient. Use (P1) with
$B=3m$, $\ell_w=|I_w|$ and
$Q=\lceil6m/\ell_w\rceil$. Then

$$
H(\theta_m,Q)<\frac{6m}Q\le\ell_w.
$$

Translating the entire point set by $\theta_m$ preserves its circular
gaps. Consequently one of
$\theta_m,2\theta_m,\ldots,(Q+1)\theta_m$ lies in the open arc $I_w$.
This supplies a positive multiplier, rather than merely the zero orbit
point. With $K_w=6\varphi^h+2$, there is an integer $k$ such that

$$
1\le k\le K_wm,\qquad
H=km\in C_w,\qquad m\le H\le K_wm^2.
\tag{P3}
$$

The constant depends on the fixed prefix. This is a direct application
of (P1), not a new quantitative Kronecker theorem.

## Relative Robin saturation survives every fixed prefix

Write $Z(n)=\sigma(n)/n=\sum_{d\mid n}d^{-1}$ and
$R(n)=Z(n)/(e^\gamma\log\log n)$ for sufficiently large $n$.
The classical Grönwall theorem supplies $m_i\to\infty$ with
$R(m_i)\to1$ and the global upper limsup one. Apply (P3) to each $m_i$.
For the same actual integer $H_i=k_im_i\in C_w$, divisor inclusion and
the size bound give

$$
Z(H_i)\ge Z(m_i),\qquad
\log m_i\le\log H_i\le2\log m_i+\log K_w,
\qquad
\frac{\log\log m_i}{\log\log H_i}\longrightarrow1.
$$

No coprimality assumption on $k_i,m_i$ is needed. Therefore
$\liminf_i R(H_i)\ge1$, while the global Grönwall upper limsup gives
$\limsup_i R(H_i)\le1$. The resulting application is

$$
\limsup_{\substack{n\to\infty\\n\in C_w}}
\frac{\sigma(n)}{e^\gamma n\log\log n}=1
\quad\text{for every fixed legal prefix }w.
\tag{P4}
$$

In particular, no such cylinder has an eventual bound
$R(n)\le1-\delta_w$ for a fixed $\delta_w>0$.
Every nonempty class determined solely by finitely many fixed low
windows and the unit digit contains one of these cylinders and has
the same upper limsup. Intersecting a class with CA identity or other
prime-factor restrictions changes the population; (P4) supplies no
conclusion for that intersection.

These cylinders impose no termination constraint. A certified End
immediately after a fully observed prefix fixes a single integer;
(P4) supplies no conclusion for additional End or length restrictions.

## The additive sign and the original source remain unpaid

For $m>e$ and a multiplier in (P3), the exact additive ledger is

$$
\begin{aligned}
\Delta(km)-\Delta(m)
&=e^\gamma\log\!\left(1+\frac{\log k}{\log m}\right)
-[Z(km)-Z(m)],\\
\Delta(n)&=e^\gamma\log\log n-Z(n).
\end{aligned}
$$

The first term is allowed to reach $e^\gamma\log2+o(1)$ by the
available size bound; only nonnegativity is known for the bracketed
term. Thus (P4) supplies neither additive convergence to zero nor
the strict Robin sign. Its guaranteed relative denominator loss is
$O_w(1/\log\log m)$, which at $\log m\asymp P$ is
$O_w(1/\log P)$, too coarse for the
$1/(\sqrt P\log P)$ comparison needed at an actual CA host.
The construction also supplies no preservation of prime support,
ordered exponents or CA identity.

The finer near-zero CA-host comparator is already available in
[Baker's source application](baker2021smoothbeatty.md); it should be
reused on its stated branch. The
[multiplicative Beatty average](../ArithSums/guloglunevans2008beatty.md)
does not bound an individual extremal integer. The
[complete Robin comparison](../ArithSums/nicolas2025comparison.md),
GPP7, still requires the full same-source signed once-prime estimate.
Neither (P4) nor a change of FIB coordinates supplies it. The
all-integer strict Robin inequality and RH remain unresolved here.
