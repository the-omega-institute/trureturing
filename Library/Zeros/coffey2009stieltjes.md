---
bibkey: coffey2009stieltjes
authors: Mark W. Coffey
year: 2009
title: The Stieltjes constants, their relation to the eta_j coefficients, and representation of the Hurwitz zeta function
doi: null
url: https://arxiv.org/abs/0706.0343v2
claim: Proposition 2(a) splits the Li arithmetic contribution into a Stieltjes term and an ordered von Mangoldt sum; standard orthogonal coefficient budgets control the Stieltjes and proper-prime-power channels, while the centered primary-prime joint estimate remains unproved.
strata_touched: []
license: citation-only
triage: anchor
---

# Stieltjes and prime-power parts of the Li joint estimate

The primary is Mark W. Coffey,
[arXiv:0706.0343v2](https://arxiv.org/abs/0706.0343v2), version
25 February 2009, first submitted in 2007. Source locators below refer
to that version. Proposition 2(a), equations (12), (14)--(17), supplies
the decomposition. The integral representation and orthogonal coefficient
budgets below are applications of standard Euler--Maclaurin and Laguerre
identities, not a new version of those results or a priority claim.
The adjacent-Fibonacci consumer reuses Lagarias's Weil kernel. This is
paper mathematics without Lean certification; the actual signed prime
estimate and RH remain unproved.

## CS1. Exact normalization and the ordered prime-power term

Use the classical constants with conventions

$$
\zeta(1+s)=\frac1s+\sum_{k\ge0}\frac{(-1)^k\gamma_k}{k!}s^k,
\qquad
-\frac{\zeta'}\zeta(1+s)=\frac1s+\sum_{k\ge0}\eta_ks^k.
$$

Coffey's Proposition 2(a) gives, for each integer $n\ge1$,

$$
S_2(n)=-\sum_{r=1}^n\binom nr\eta_{r-1}
=S_\gamma(n)+S_\Lambda(n),
\qquad
S_\gamma(n)=\sum_{r=1}^n\frac{(-1)^r}{(r-1)!}
                      \binom nr\gamma_{r-1},
\tag{CS1}
$$

$$
S_\Lambda(n)=n+\lim_{X\to\infty}\sum_{2\le m\le X}
  \frac{1-\Lambda(m)}m L_{n-1}^{(1)}(\log m).
\tag{CS2}
$$

Here $\Lambda(p^k)=\log p$ for every prime power, and vanishes otherwise.
The sum is in increasing integer order, not an absolutely convergent
prime-only sum. For fixed $n$, its convergence follows by partial
summation from the [existing unconditional PNT supplier](../Weil/johnstonyang2022pnt.md),
which in particular gives the classical weaker remainder
$\sum_{m\le x}(\Lambda(m)-1)=O(xe^{-c\sqrt{\log x}})$ for some $c>0$.
No uniform-in-$n$ estimate follows from this fixed-polynomial argument.
The $m=1$ contribution is exactly $L_{n-1}^{(1)}(0)=n$ and is retained.

Let $H_n=S_\infty(n)+1$ in the classical specialization of Lagarias,
published Lemma 4.4, equations (4.5)--(4.8). The exact split is
$\lambda_n=H_n+S_2(n)$. Put

$$
U_n=n+S_\gamma(n),\qquad
P_n=\lim_{X\to\infty}\sum_{2\le m\le X}
 \frac{\Lambda(m)-1}m L_{n-1}^{(1)}(\log m).
$$

Then, with the same Li normalization as
[the Fibonacci growth application](lagarias2007li.md),

$$
\boxed{\lambda_n=H_n+U_n-P_n.}
\tag{CS3}
$$

All three indices used below refer to this single actual arithmetic
sequence. They are not independently optimized prime configurations.

## CS2. Source-use scope of the reported linear bound

Proposition 2(b) reports $S_\gamma(n)=O(n)$. Its displayed proof,
equation (52), replaces a bounded periodic Bernoulli factor by a
constant and then integrates a signed Laguerre polynomial. That step
does not bound the absolute integral: the polynomial changes sign.
Equations (49) and (51) also print boundary signs that are not adopted
here. These observations do not establish that Proposition 2(b) is
false. Its linear-growth conclusion follows independently from the
standard orthogonal argument below; the displayed source majorization
is not used. The stronger Corollary 16 rate is not imported.

## CS3. A finite orthogonal budget for the Stieltjes channel

Write $P_1(t)=\{t\}-1/2$. The standard Euler--Maclaurin formula
[DLMF 25.11.5](https://dlmf.nist.gov/25.11.E5), with $a=1$, $N=0$,
gives, initially for $\Re s>1$ and then near $s=1$ after pole removal,

$$
\zeta(s)=\frac1{s-1}+\frac12
 -s\int_1^\infty P_1(t)t^{-s-1}\,dt.
\tag{CS4}
$$

The integral and all fixed-order derivatives converge locally uniformly
near one. Coefficient comparison with CS1 gives

$$
\gamma_k=\frac{\mathbf1_{k=0}}2+
 \int_1^\infty\frac{P_1(t)}{t^2}
       \bigl[k(\log t)^{k-1}-(\log t)^k\bigr]dt,
$$

where the first summand inside the brackets is zero for $k=0$.
The finite binomial sum in CS1, the derivative identity
[DLMF 18.9.23](https://dlmf.nist.gov/18.9.E23), and the contiguous identity
[DLMF 18.9.13](https://dlmf.nist.gov/18.9.E13) therefore yield

$$
S_\gamma(n)=-\frac n2+
 \int_0^\infty P_1(e^u)e^{-u}L_{n-1}^{(2)}(u)\,du.
\tag{CS5}
$$

For $n=1$ this reads $S_\gamma(1)=-\gamma$, consistently with CS1.
Put $p_n=L_{n-1}^{(2)}$. Telescoping the contiguous identity gives
$p_n=\sum_{k=0}^{n-1}(n-k)L_k^{(0)}$. Orthogonality against
$L_0^{(0)}=1$ therefore gives $\int_0^\infty e^{-u}p_n(u)du=n$.
Writing $F(u)=\{e^u\}=P_1(e^u)+1/2$ in CS5 yields the exact identity

$$
U_n=n+S_\gamma(n)=\int_0^\infty F(u)e^{-u}p_n(u)\,du.
$$

Here is the standard coefficient budget used for this and the
higher-power channel below. For measurable $g$ with

$$
\mathcal N(g)^2:=\int_0^\infty\frac{e^{-u}|g(u)|^2}{u^2}du<\infty,
\qquad
c_n(g)=\int_0^\infty g(u)e^{-u}p_n(u)du,
$$

work in $L^2((0,\infty),u^2e^{-u}du)$ with $f=g/u^2$.
The Laguerre row of
[DLMF Table 18.3.1](https://dlmf.nist.gov/18.3.T1) gives the
orthonormal sequence $p_n/\sqrt{n(n+1)}$.
[Bessel's inequality](https://dlmf.nist.gov/1.18.E2) gives

$$
\boxed{\sum_{n\ge1}\frac{|c_n(g)|^2}{n(n+1)}
       \le\mathcal N(g)^2.}
\tag{CS6}
$$

For $F$, one has $F(u)=e^u-1=O(u)$ near zero and $0\le F(u)<1$
everywhere. Thus $\mathcal N(F)<\infty$, and CS6 proves

$$
\boxed{\sum_{n\ge1}\frac{|U_n|^2}{n(n+1)}\le\mathcal N(F)^2<\infty,
\qquad U_n=o(n),\qquad S_\gamma(n)=-n+o(n).}
\tag{CS7}
$$

The little-$o$ conclusion follows because the summands tend to zero
and $\sqrt{n(n+1)}/n\to1$. No completeness or Parseval equality is
needed. This supplies the reported $S_\gamma(n)=O(n)$ conclusion
independently of the source's displayed proof. It does not certify
Corollary 16's stronger $U_n=O(n^{1/4})$ rate or bound $P_n$.

## CS4. Consumer: the original adjacent-Fibonacci joint matrix

Put $a=F_{j-1}$, $b=F_j$, $c=F_{j+1}=a+b$, for $j\ge3$.
Lagarias's published Theorem 3.1, equations (3.3)--(3.4), supplies the
actual Weil matrix on its Li test functions $G_b,G_c$:

$$
K_j=\begin{pmatrix}
 2\lambda_b&\lambda_b+\lambda_c-\lambda_a\\
 \lambda_b+\lambda_c-\lambda_a&2\lambda_c
\end{pmatrix}.
\tag{CS8}
$$

Its positivity is not supplied by the word "matrix" or "Weil": without
RH this Hermitian form is not known to be positive. Set

$$
h_n=H_n+U_n,\quad q_j=h_b+h_c-h_a,\quad
 e_j=P_b+P_c-P_a,\quad D_j=4h_bh_c-q_j^2.
$$

Direct expansion of the same actual CS8, retaining every cross term,
is the exact bookkeeping identity

$$
\det K_j=D_j-E_j,\qquad
E_j=4(h_cP_b+h_bP_c)-2q_je_j+e_j^2-4P_bP_c,
\tag{CS9}
$$

$$
\operatorname{tr}K_j=2(h_b+h_c-P_b-P_c).
\tag{CS10}
$$

Lagarias's unconditional Theorem 5.1 supplies
$H_n=\tfrac12n\log n+\tfrac12(\gamma-1-\log(2\pi))n+O(1)$.
Combining it with the sufficient CS7, and using that $a/b$ and $c/b$
stay bounded above and away from zero, gives

$$
D_j=ab(\log b)^2+O\bigl(b^2\log b\bigr),
\qquad
2(h_b+h_c)=(b+c)\log b+O(b).
\tag{CS11}
$$

Indeed $h_t=\tfrac12t\log b+O(b)$ for
$t\in\{a,b,c\}$; the leading terms in $4h_bh_c-q_j^2$ are
$bc(\log b)^2-b^2(\log b)^2=ab(\log b)^2$.
Both controlled baselines are eventually positive. The missing
arithmetic estimates remain, jointly for every sufficiently large $j$,

$$
\boxed{P_b+P_c\le h_b+h_c,\qquad E_j\le D_j.}
\tag{CS12}
$$

Together they are equivalent to eventual positive semidefiniteness of
the actual real symmetric CS8, by its trace and determinant. No bound
for CS12 is proved here. Separate bounds must hold simultaneously for the same actual sequence
and be quantitatively strong enough to imply both coupled inequalities.
Separately attainable row configurations cannot be combined as one
realization.

This controlled Stieltjes contribution is sufficient for CS11; it is
not an upper bound on $P_n$, $E_j$, $\lambda_n$ or the Robin response.
The Fibonacci absolute-growth bound, the original joint signed Robin
estimate, the endpoint half-variance bound and RH remain unresolved.

## CS5. The higher-prime-power channel has a finite Laguerre energy

The higher-prime-power estimates for compact autocorrelation tests in the
[weighted Mertens application](../Weil/broadbent2026mertens.md) retain their
original test class and derivative norm. They are not substituted for a
bound on the noncompact linear Laguerre row here. Instead, the standard
Laguerre orthogonality already used in CS3 supplies a direct application
to this actual row. No new prime-distribution theorem, priority claim,
Lean certification or primary-prime estimate is asserted.

For $n\ge1$, retain every proper prime power in

$$
B_n=\sum_{p\in\mathbb P}\sum_{k\ge2}
 \frac{\log p}{p^k}L_{n-1}^{(1)}(k\log p),
\qquad
A(u)=\psi(e^u)-\vartheta(e^u)
    =\sum_{\substack{p\in\mathbb P,\ k\ge2\\k\log p\le u}}\log p.
\tag{CS13}
$$

Here $\mathbb P$ is the set of primes,
$\psi(x)=\sum_{m\le x}\Lambda(m)$ and
$\vartheta(x)=\sum_{p\le x}\log p$. Each proper prime power is counted
once with its von Mangoldt weight. In particular $A(u)=0$ on
$0\le u<\log4$; the unit endpoint from CS2 is not inserted again.

The [existing Rosser--Schoenfeld source](../Arith/rosser1962approximate.md),
Theorem 13, equation (3.36), printed p.71, directly supplies

$$
0\le\psi(x)-\vartheta(x)<\kappa\sqrt x\quad(x>0),
\qquad \kappa=1.42620.
$$

This bound includes the full proper-prime-power sum. It gives the
independently defined finite budget

$$
C_A^2:=\int_0^\infty\frac{e^{-u}A(u)^2}{u^2}\,du
\le\frac{\kappa^2}{\log4}<\infty.
\tag{CS14}
$$

There is no origin singularity because $A$ vanishes before $\log4$;
at infinity the integrand is bounded by $\kappa^2/u^2$. No estimate of the
primary-prime discrepancy or assumption about zeta zeros is needed.

For fixed $n$, CS13 is absolutely convergent. Stieltjes integration by
parts, with the boundary terms zero at both zero and infinity, uses

$$
\frac d{du}\left(e^{-u}L_{n-1}^{(1)}(u)\right)
=-e^{-u}L_{n-1}^{(2)}(u)
$$

from the same DLMF derivative and contiguous identities used in CS3. Thus

$$
B_n=\int_0^\infty A(u)e^{-u}L_{n-1}^{(2)}(u)\,du.
\tag{CS15}
$$

Since $C_A=\mathcal N(A)$, CS6 applies directly with $g=A$.
Thus, for every finite partial sum and then its monotone limit,

$$
\boxed{\sum_{n\ge1}\frac{|B_n|^2}{n(n+1)}\le C_A^2<\infty.}
\tag{CS16}
$$

In particular $|B_n|\le C_A\sqrt{n(n+1)}$ for every $n\ge1$, and

$$
\boxed{B_n=o(n).}
\tag{CS17}
$$

No completeness assertion or Parseval equality is needed. This is a
standard orthogonal coefficient estimate with its actual arithmetic
input identified, not an estimate obtained by assigning the Robin
slack to a norm.

## CS6. The same joint matrix with a centered primary-prime row

Set $Q_n=P_n-B_n$ and $h_n^*=H_n+U_n-B_n$. Absolute convergence of
CS13 permits the exact same-cutoff expression

$$
Q_n=\lim_{X\to\infty}\left[
 \sum_{p\le X}\frac{\log p}{p}L_{n-1}^{(1)}(\log p)
 -\sum_{2\le m\le X}\frac1mL_{n-1}^{(1)}(\log m)\right].
\tag{CS18}
$$

Both terms retain the common cutoff. Neither divergent summand is
assigned a separate value. The actual Li identity is now
$\lambda_n=h_n^*-Q_n$, with no prime power discarded.

The controlled combination also has a common-source budget, not just
two separately chosen estimates:

$$
\sum_{n\ge1}\frac{|U_n-B_n|^2}{n(n+1)}
\le\mathcal N(F-A)^2<\infty.
$$

This is CS6 applied to the one actual function $F-A$; its norm is
finite by the triangle inequality. Consequently
$h_n^*=H_n+o(n)$.

For the same adjacent Fibonacci triple, the complete higher-power
matrix contribution is

$$
\mathcal B_j=\begin{pmatrix}
2B_b&B_b+B_c-B_a\\
B_b+B_c-B_a&2B_c
\end{pmatrix},\qquad \|\mathcal B_j\|_{\mathrm{op}}=o(b).
\tag{CS19}
$$

Indeed all three indices are comparable and CS17 holds for every
integer index. This is a bound on that component of the actual joint
matrix, without a sign assertion about its entries. The baseline CS11
remains valid with $h$ replaced by $h^*$, since $B_t=o(t)$.

Equations CS9--CS10 apply exactly with $(h,P)$ replaced by $(h^*,Q)$.
Their coupled trace and determinant inequalities on this one actual
centered prime sequence remain unproved. In particular every mixed
$B$--$Q$ contribution is retained through $h^*$, rather than omitted
from a determinant expansion. CS16--CS19 control the higher-power
channel; they supply no growth bound for $Q_n$ or $\lambda_n$, no
signed Robin estimate, and no proof of RH.

## CS7. The critical primary-prime energy is an RH-level premise

The staircase of the actual same-cutoff row CS18 is

$$
T(u)=\vartheta(e^u)-\lfloor e^u\rfloor+1,
\qquad T(u)=0\quad(0\le u<\log2).
$$

Its Stieltjes measure has weight $\log p$ at each primary prime and
weight $-1$ at each integer at least two. Applying the derivative
identity in CS5 to this single staircase gives, for each fixed $n$,

$$
Q_n=\int_0^\infty T(u)e^{-u}p_n(u)\,du=c_n(T).
\tag{CS20}
$$

The lower boundary term is zero. The existing PNT supplier makes the
upper boundary term tend to zero and the last integral absolutely
convergent for each fixed polynomial $p_n$. This does not imply a
uniform bound as $n$ grows. It preserves the common cutoff in CS18;
neither divergent summand is separately assigned a value.

Define, for $\eta\in\{\vartheta,\psi\}$,

$$
J_\eta=\int_2^\infty
 \frac{|\eta(x)-x|^2}{x^2(\log x)^2}\,dx.
$$

The change of variable $x=e^u$ identifies $\mathcal N(T)^2$ with
the same integral using $\vartheta(x)-\lfloor x\rfloor+1$ in the
numerator. Its difference from $\vartheta(x)-x$ is $\{x\}+1$,
a bounded function with finite weighted norm on $[2,\infty)$.
The Rosser--Schoenfeld bound in CS5 also gives a finite weighted norm
for $\psi-\vartheta$, since
$\int_2^\infty dx/[x(\log x)^2]<\infty$. Thus

$$
\mathcal N(T)<\infty
\quad\Longleftrightarrow\quad J_\vartheta<\infty
\quad\Longleftrightarrow\quad J_\psi<\infty.
\tag{CS21}
$$

The [classical Cramér square-mean estimate](cramer1922mittelwert.md),
printed p.147, supplies **under RH**
$M(X):=\int_2^X|\psi(t)-t|^2/t\,dt=O(X)$.
For $k\ge1$, its contribution to $J_\psi$ on $[2^k,2^{k+1}]$ is at most

$$
\frac{M(2^{k+1})}{2^k(k\log2)^2}=O(k^{-2}).
$$

Summing proves $J_\psi<\infty$ under RH. The classical mean-square
result is reused with its stated weight and hypothesis; the dyadic
transfer is its parameter application to CS21.

Conversely, if $\mathcal N(T)<\infty$, the already established CS6
and CS20 give $Q_n=o(n)$. The exact CS3/CS18 split and CS7/CS17 then give
$\lambda_n=H_n+o(n)=O(n\log n)$. This absolute growth implies RH
by Lagarias's published all-index criterion, Theorem 2.2(3), equation
(2.22), already used in the [Fibonacci growth application](lagarias2007li.md).
No new completeness assertion, zero truncation or sign-sensitive
Theorem 6.1 is needed. Consequently the exact strength of this proposed
budget is

$$
\boxed{\mathcal N(T)<\infty\quad\Longleftrightarrow\quad\mathrm{RH}.}
\tag{CS22}
$$

This is a paper application of classical sources and the existing
coefficient interface, without Lean certification or a priority claim.
It classifies a possible sufficient route; no unconditional finite
energy or new actual prime estimate has been acquired. Proving that
energy finite remains a legitimate RH strategy, but assuming it does
not supply an independently available reserve. The original signed
trace/determinant conditions remain unpaid; a norm is not imposed as
the necessary intermediate mechanism for any particular finite triple.
The original Robin estimate and endpoint half-variance bound also
remain unresolved.

## CS8. A uniform arithmetic tail for growing Li tests

The following parameter application controls the omitted part of the
actual ordered CS18 row simultaneously for growing degrees. It uses
the existing PNT supplier and the classical finite Laguerre series;
it is not a new prime-distribution estimate or a priority claim.
The finite signed head, the original joint inequalities and RH remain
unresolved. No numerical execution or practical cutoff claim is made.

For an integer $X\ge3$, let $Q_n(X)$ be the bracket in CS18 before
taking its limit, with the same cutoff in both sums, and put $U=\log X$.
The exact finite-endpoint identity behind CS20 gives

$$
Q_n-Q_n(X)=\int_U^\infty T(u)e^{-u}p_n(u)\,du
 -e^{-U}L_{n-1}^{(1)}(U)T(U).
\tag{CS23}
$$

In particular the upper boundary term is retained. The
[Johnston--Yang estimate](../Weil/johnstonyang2022pnt.md),
Theorem 1.1, and the Rosser--Schoenfeld complete higher-power bound
already used in CS5 give, for $u\ge\log2$,

$$
\begin{gathered}
|T(u)|\le e^u\varepsilon(u),\\
\varepsilon(u)=9.39u^M e^{-d\sqrt u}
 +\kappa e^{-u/2}+2e^{-u},\qquad
M=1.515,\quad d=0.8274,\quad\kappa=1.42620.
\end{gathered}
$$

Indeed $T=(\psi(e^u)-e^u)-A(u)+\{e^u\}+1$. This uses the
all-prime-power PNT statement and the full $A$, with no global RH
premise or discarded prime powers.

Coffey's equation (64), with $(\nu,n)=(1,n)$ and $(2,n+1)$,
is the classical terminating-series identity

$$
L_{n-1}^{(\alpha)}(u)
=\sum_{k=0}^{n-1}(-1)^k
 \binom{n-1+\alpha}{n-1-k}\frac{u^k}{k!},
\qquad \alpha\in\{1,2\}.
$$

For $u\ge1$ and $1\le n\le N$, each $u^k/k!$ is at most
$u^{N-1}$ and the binomial coefficient sum is at most $2^{N+1}$.
Applying this bound to both terms of CS23 gives the explicit allowance

$$
\boxed{
\sup_{1\le n\le N}|Q_n-Q_n(X)|\le\mathcal E_N(U)
:=2^{N+1}\left[
U^{N-1}\varepsilon(U)
+\int_U^\infty u^{N-1}\varepsilon(u)\,du\right],
\quad U\ge1.
}
\tag{CS24}
$$

All terms on the right refer to one common cutoff. This controls both
signs of the omitted ordered tail, rather than assigning separate
values to its divergent prime and integer sums.

One deterministic analytical cutoff is
$X_N=\lceil\exp(N^4)\rceil$. There are constants $C_*>0$ and an
integer $N_0$ such that, for every $N\ge N_0$ and every integer $X$
with $\log X\ge N^4$,

$$
\mathcal E_N(\log X)\le C_*e^{-\delta N^2},
\qquad \delta=d/4>0.
\tag{CS25}
$$

Here the constants are independent of $n,N,X$. To verify the uniform
quantifier, completing squares gives, for $u\ge1$,

$$
\varepsilon(u)\le C_\varepsilon u^M e^{-d\sqrt u},
\qquad C_\varepsilon=9.39+\kappa e^{d^2/2}+2e^{d^2/4}.
$$

Since $\log u/\sqrt u$ decreases on $[e^2,\infty)$, for all
sufficiently large $N$ and every $u\ge N^4$,

$$
\frac{(N+1)\log2+(N-1+M)\log u}{\sqrt u}
\le\frac{(N+1)\log2+4(N-1+M)\log N}{N^2}
\le d/2.
$$

Thus the integrand and endpoint in CS24 are bounded by
$C_\varepsilon e^{-d\sqrt u/2}$, giving

$$
\mathcal E_N(U)\le
C_\varepsilon\left(1+\frac{4\sqrt U}{d}+\frac8{d^2}\right)
e^{-d\sqrt U/2}.
$$

Absorbing this polynomial factor into $e^{d\sqrt U/4}$ proves CS25.
The threshold is an analytical existence statement; no scan, numerical
optimization or efficient computation is asserted.

For the actual adjacent Fibonacci triple $a,b,c$, set $N=c$ and use
the common integer $X_c$. Define
$\lambda_n^{(X)}=h_n^*-Q_n(X)$ for $n\in\{a,b,c\}$, retaining
the actual full $h^*=H+U-B$. Let $K_j^{(X)}$ be CS8 with these
three values substituted. With $\epsilon_c=C_*e^{-\delta c^2}$,
the diagonal errors are at most $2\epsilon_c$ and the off-diagonal
error at most $3\epsilon_c$. The maximum absolute row sum therefore
gives the whole real symmetric matrix allowance

$$
\boxed{\|K_j-K_j^{(X_c)}\|_{\mathrm{op}}\le5\epsilon_c}
\quad\text{for every sufficiently large }j.
\tag{CS26}
$$

Every mixed contribution and the unit endpoint remain in the original
exact split. This upgrades fixed-degree convergence to a simultaneous
bound for this growing family. It supplies no eventual sign for the
finite-head matrices $K_j^{(X_c)}$; that common-source signed comparison
is still required. Finite truncation with a small omitted-tail allowance
is not a verification over all Fibonacci indices, a Robin estimate,
the endpoint half-variance bound, or a proof of RH. This application
has no new Lean certification.


## CS9. A classical bound pays the growing low-prime prefix

The [classical uniform Laguerre bound](../Estimation/plewa2018laguerre.md)
as reproduced in Plewa, Section 4, equation (19), applies to the actual
finite CS18 row with the same inclusive integer cutoff. This is a
parameter application of that existing estimate, not a new polynomial
or prime-distribution theorem, numerical validation or priority claim.

There are constants $C_0,N_0$ such that for every integer $N\ge N_0$
and every integer $N/3\le n\le N$,

$$
\boxed{|Q_n(N)|\le\eta_N
:=C_0N^{3/4}(\log N)^{1/4}=o(N).}
\tag{CS27}
$$

To apply the source, its standard function at degree $n-1$ and
parameter $1$ is exactly
$\mathcal L_{n-1}^1(u)=\sqrt{u/n}\,e^{-u/2}L_{n-1}^{(1)}(u)$.
The cited estimate, with $\nu=4n$, therefore gives

$$
|L_{n-1}^{(1)}(u)|\le Cn^{1/4}e^{u/2}u^{-3/4},
\qquad(4n)^{-1}<u\le2n.
$$

Its constant is independent of $n,u$. For all sufficiently large $N$,
$(4n)^{-1}<\log2$ and $\log N\le2n$ hold throughout
$N/3\le n\le N$. Consequently the bound holds on the entire growing
interval $\log2\le u\le\log N$ needed by both finite sums. It is not
an application of a fixed-$u$ asymptotic with uncontrolled constants.
Using only that primes form a subset of the integers gives

$$
\begin{aligned}
\left|\sum_{p\le N}\frac{\log p}{p}
 L_{n-1}^{(1)}(\log p)\right|
&\le Cn^{1/4}(\log N)^{1/4}\sum_{2\le m\le N}m^{-1/2}
\le2CN^{3/4}(\log N)^{1/4},\\
\left|\sum_{2\le m\le N}\frac1m
 L_{n-1}^{(1)}(\log m)\right|
&\le Cn^{1/4}(\log2)^{-3/4}\sum_{2\le m\le N}m^{-1/2}
\le2C(\log2)^{-3/4}N^{3/4}.
\end{aligned}
$$

The triangle inequality proves CS27 after absorbing the fixed second
constant. Indeed $\eta_N/N=C_0(\log N/N)^{1/4}\to0$.
No cancellation or prime-counting theorem is used. Both sums keep
$p\le N$ and $2\le m\le N$ exactly, and the unit endpoint is not moved.

For the original adjacent Fibonacci triple $a,b,c$, all three indices
lie in $[c/3,c]$. Keep CS25's single integer
$X_c=\lceil\exp(c^4)\rceil$ and define the actual remaining middle by

$$
Q_n^{\rm mid}=Q_n(X_c)-Q_n(c),\qquad
\lambda_n^{\rm mid}=h_n^*-Q_n^{\rm mid},\qquad n\in\{a,b,c\}.
$$

Thus the middle sums have $c<p\le X_c$ and $c<m\le X_c$;
$h^*=H+U-B$ remains whole. In particular all proper prime powers and
the unit endpoint remain in their existing channels. With
$q_n=Q_n(c)$ and $r_n=Q_n-Q_n(X_c)$, the exact relation is
$\lambda_n^{\rm mid}-\lambda_n=q_n+r_n$.
Let $\mathcal M(z_a,z_b,z_c)$ denote CS8's linear matrix map. Then

$$
K_j^{\rm mid}-K_j
=\mathcal M(q_a+r_a,q_b+r_b,q_c+r_c),
$$

with the original off-diagonal combination retained. Applying the
same row-sum allowance as CS26 gives, for every sufficiently large
Fibonacci index,

$$
\boxed{\|K_j^{\rm mid}-K_j\|_{\rm op}
\le5\left(\eta_c+C_*e^{-\delta c^2}\right)=o(c).}
\tag{CS28}
$$

This pays the actual growing low-prime prefix and carries the already
paid remote tail, leaving the actual middle interval in the original
signed matrix. It does not bound the sign of that middle or establish
its eventual positivity. The original complete joint estimate, Robin,
the endpoint half-variance bound and RH remain unresolved. This
application has no new Lean certification.

## CS10. Two weaker signed targets on the actual middle

Keep the actual middle and the full $h^*$ from CS9. Instead of requiring
positivity of the whole $K_j^{\rm mid}$, consider the following pair of
**unproved** estimates: there is one $C>0$ such that for every sufficiently
large adjacent Fibonacci triple $a,b,c$,

$$
\boxed{\lambda_c^{\rm mid}\ge-Cc^2,\qquad
2\lambda_a^{\rm mid}+2\lambda_b^{\rm mid}-\lambda_c^{\rm mid}
\ge-Cc^2.}
\tag{CS29}
$$

The first scalar is half the second diagonal entry of $K_j^{\rm mid}$;
the second is $(2,-1)K_j^{\rm mid}(2,-1)^{\mathsf T}/2$.
Thus positive semidefiniteness would imply both. Their exact arithmetic
requirements, keeping every term of $h^*$, are

$$
\begin{aligned}
Q_c^{\rm mid}&\le h_c^*+Cc^2,\\
2Q_a^{\rm mid}+2Q_b^{\rm mid}-Q_c^{\rm mid}
&\le2h_a^*+2h_b^*-h_c^*+Cc^2.
\end{aligned}
\tag{CS30}
$$

CS28 transfers each scalar to the actual Li coefficients with $o(c)$
error. Increasing a constant would therefore give
$\lambda_c\ge-C'c^2$ and
$\lambda_c\le2\lambda_a+2\lambda_b+C'c^2$, whence

$$
|\lambda_c|\le2|\lambda_a|+2|\lambda_b|+C'c^2.
$$

Since $a/c\in[1/3,1/2]$,
$2a^3+2b^3=2c^3[1-3(a/c)+3(a/c)^2]\le2c^3/3$.
Choose $D\ge3C'$ large enough to cover the two Fibonacci seeds before
the eventual recurrence begins. Induction would then give
$|\lambda_{F_j}|\le DF_j^3$: the recurrence is at most
$2Dc^3/3+C'c^2\le Dc^3$. The existing
[Fibonacci absolute-growth criterion](lagarias2007li.md#fibonacci-sampled-absolute-growth-a-paper-criterion)
would imply RH.

This is a sufficient unpaid target, not an estimate of the actual
middle or a new unconditional RH result. Deriving another sufficient
condition alone does not supply arithmetic cancellation. The argument
is a paper application of the existing matrix transport and growth
criterion, without Lean certification or a priority claim.

## CS11. The prescribed absolute PNT allowance cannot pay that target

Keep CS8's $\varepsilon$, $M=1.515$ and $d=0.8274$, and CS7's
$p_n(u)=L_{n-1}^{(2)}(u)$. For integers $3\le L<X$, the same finite
Stieltjes integration by parts underlying CS23 gives, with
$k_n(u)=e^{-u}L_{n-1}^{(1)}(u)$,

$$
\begin{aligned}
Q_n(X)-Q_n(L)={}&\int_{\log L}^{\log X}T(u)e^{-u}p_n(u)\,du\\
&+k_n(\log X)T(\log X)-k_n(\log L)T(\log L).
\end{aligned}
$$

Both endpoints remain. For the second CS30 combination define

$$
J_c(u)=2p_a(u)+2p_b(u)-p_c(u),\qquad
\mathcal A_j=\int_{\log c}^{\log X_c}
\varepsilon(u)|J_c(u)|\,du.
\tag{CS31}
$$

This is an absolute **comparison allowance**, obtained by replacing
$e^{-u}|T(u)|$ with its CS8 upper bound. It is not the actual signed
integral or its absolute value. Adding the absolute values of the two
joint endpoint terms only increases this allowance. Even this integral
part satisfies

$$
\boxed{\mathcal A_j^{1/c}\longrightarrow\infty.}
\tag{CS32}
$$

To apply the classical terminating Laguerre series already cited in
CS8, take the single analytical interval
$I_c=[4c^2,4c^2+1]$. It is contained in
$[\log c,\log X_c]$ for all sufficiently large $c$.
For $1\le r\le n-1$, the absolute ratio of the $r$-th subleading
term of $p_n$ to $u^{n-1}/(n-1)!$ is

$$
\binom{n+1}{r}\frac{(n-1)!}{(n-1-r)!}\,u^{-r}
\le\frac1{r!}\left(\frac{n^2-1}{u}\right)^r\le4^{-r},
\qquad n\le c,\ u\ge4c^2.
$$

Their sum is at most $\sum_{r\ge1}4^{-r}=1/3$. Thus

$$
\frac23\frac{u^{n-1}}{(n-1)!}
\le|p_n(u)|\le\frac43\frac{u^{n-1}}{(n-1)!},
\qquad 1\le n\le c,\ u\ge4c^2.
\tag{CS33}
$$

For $n=1$ the subleading sum is empty. Taking ratios gives
$|p_b|/|p_c|\le2(c/u)^{c-b}\le2(4c)^{-a}$ and
$|p_a|/|p_c|\le2(4c)^{-b}$ on $I_c$.
As $a,b\to\infty$, the triangle inequality therefore gives
$|J_c|\ge|p_c|/2\ge u^{c-1}/[3(c-1)!]$ there for every sufficiently
large Fibonacci index. The two lower degrees cannot cancel the highest
degree on this range. Using just the first positive summand of
$\varepsilon$ and $\sqrt{4c^2+1}\le2c+1$ yields

$$
\mathcal A_j\ge\frac{9.39}{3}\,
\frac{(4c^2)^{c-1+M}}{(c-1)!}\,e^{-d(2c+1)}.
\tag{CS34}
$$

Replacing $(c-1)!$ by $c^{c-1}$ in the denominator of CS34 gives a
coarser lower bound. The $c$-th root of that coarser bound divided by
$c$ has limit $4e^{-2d}>0$, proving CS32. This is a finite-series
parameter application on one fixed analytical interval, with no
numerical execution, cutoff optimization, new Laguerre theorem or
literature-priority claim.

Consequently this particular absolute PNT comparison allowance cannot
have a polynomial or subexponential upper bound in $c$, even when the
Fibonacci combination is formed before taking its absolute value.
This does not lower-bound actual $T$, $Q_n^{\rm mid}$, a Li coefficient
or the signed joint form. It does not rule out further signed arithmetic
information, exact endpoint cancellation or a different representation.
What remains unpaid is an estimate of the actual same-source middle
with both endpoints, sufficient for CS29 or another valid RH route.
Robin, the complete joint estimate, endpoint half-variance and RH remain
unresolved; no new Lean certification is asserted.

## CS12. A positive-data representation with a signed inversion

The [generalized Li interface](freitas2006li.md) supplies another exact
representation of the same actual critical coefficients. Its common
finite transfer TL3 uses the actual nonnegative $\tau=2$ coefficients
$\Lambda_m(2)$, with one prescribed regularization and integer cutoff
for every $1\le n\le c$. The uniform approximation in TL4 gives the
same original Fibonacci matrix a whole-matrix error
$5Ce^{-c^2/2}$ for all sufficiently large indices. This is an
approximation-error estimate, not a sign or growth bound on the
critical Li coefficients or the actual arithmetic middle.

At $\tau=2$ a classical Poisson representation gives an unconditional
positive semidefinite comparison matrix. Returning to $\tau=1$ uses
signed binomial weights: the coefficient matrix already at index
$m=a<b<c$ is indefinite. Thus no termwise positivity transport is
supplied. The same-source weighted sum retains the original unresolved
sign problem; positivity of the whole transferred matrix is not
asserted. The CS29 targets, Robin, endpoint half-variance and RH remain
unproved. The source identities and estimates are directly reused;
the growing-parameter transfer is a paper application without Lean
certification, numerical execution or a literature-priority claim.

## CS13. An explicit whole-matrix transfer and its finite signed consumer

This application makes the original CS28 approximation effective, with
explicit constants and a specified starting scale. The same comparison
also supplies a finite positive bound for the original arithmetic middle.
It reuses the classical Laguerre equation and energy comparison, global
prime count, PNT tail allowance, reflected zero matrices and published
finite-height verification. These are paper applications without new
Lean certification or a literature-priority claim.

### Exact source and target

Keep CS18, CS23--CS24, CS28's exact arithmetic definition and original
matrix map. For adjacent positive Fibonacci $a\le b$, $c=a+b$, use
$X_c=\lceil\exp(c^4)\rceil$ and
$Q_n^{mid}=Q_n(X_c)-Q_n(c)$, $\lambda_n^{mid}=h_n^*-Q_n^{mid}$,
$n\in\{a,b,c\}$, with the complete $h^*=H+U-B$, every proper prime
power and both original inclusive cutoffs. First make the original
approximation effective at every such triple
with $c\ge10^{24}$, then consume it in a finite all-vector bound:

$$K_j^{mid}\succeq cI_2/50000\qquad(10^{24}\le c\le5\cdot10^{25}).$$

The matrix is the ORIGINAL actual arithmetic middle, not a new surrogate
or a scalar Li-positivity inference. The full RH/strictRobin target
remains unchanged and unproved.

### An explicit finite comparison from the classical equation

The standard uniform Laguerre estimate already supplies the shape of the
prefix bound, and is reused as background rather than presented as new.
For a finite constant use the classical differential equation in
[DLMF Table 18.8.1](https://dlmf.nist.gov/18.8#T1), its Laguerre row,
with degree $n-1$ and parameter $1$. Together with the usual Liouville
change of variable and energy/Gronwall estimate it permits the following
explicit parameter comparison, without any unknown asymptotic start.

Write $L=\log c$, $x_0=1/n$ and

$$
Y(x)=xe^{-x/2}L_{n-1}^{(1)}(x),\qquad p(x)=n/x-1/4.
$$

The cited equation gives $Y''+pY=0$. For every $c\ge10^{24}$,
$(\log c)/c$ decreases and $\log(10^{24})<60$, so $L<c/3\le n$.
Throughout $x_0\le x\le L$, therefore $x\le n$ and
$p\ge3n/(4x)>0$. The terminating series already used in CS8 has
decreasing alternating terms at $x_0$. Its first two terms and the
derivative identity $(L_{n-1}^{(1)})'=-L_{n-2}^{(2)}$ give

$$
n/2\le L_{n-1}^{(1)}(x_0)\le n,\qquad
-n(n-1)/2\le(L_{n-1}^{(1)})'(x_0)\le0.
$$

Thus $0<Y(x_0)\le1$ and $0\le Y'(x_0)\le n$; for the lower derivative
bound the bracket is at least
$(1-1/(2n))n/2-(n-1)/2=1/4$.

Use the classical change $dt/dx=\sqrt p$, $V(t)=p(x)^{1/4}Y(x)$.
Its exact transformed equation is

$$
V_{tt}+(1+r)V=0,\qquad
r=\frac{5p'^2-4pp''}{16p^3}
=\frac{n(2x-3n)}{16x(n-x/4)^3}.
$$

Since $x\le n$, $|r|\le4/(9nx)$, and hence

$$
\int_{x_0}^{L}|r|\sqrt p\,dx
\le\frac4{9\sqrt n}\int_{1/n}^{L}x^{-3/2}\,dx<8/9.
$$

At $x_0$, $3n^2/4\le p(x_0)<n^2$ and $|p'(x_0)|=n^3$.
The preceding initial bounds give

$$
|V_0|\le\sqrt n,\qquad
|(V_t)_0|\le
\left((4/3)^{1/4}+\tfrac14(4/3)^{5/4}\right)\sqrt n
<\frac{16}{9}\sqrt n.
$$

The ordinary energy $E=V^2+V_t^2$ satisfies
$|dE/dt|\le|r|E$. Integrating this inequality gives

$$
|V|\le\sqrt E\le\frac{25}{9}\sqrt n\exp(4/9)
<\frac{50}{9}\sqrt n.
$$

Here $\sqrt E_0\le|V_0|+|(V_t)_0|$ and $\exp(4/9)<2$.
Returning to the original polynomial and using
$p^{-1/4}\le(4/3)^{1/4}(x/n)^{1/4}<(4/3)(x/n)^{1/4}$ yields

$$
|L_{n-1}^{(1)}(u)|\le\frac{200}{27}n^{1/4}e^{u/2}u^{-3/4}
<10n^{1/4}e^{u/2}u^{-3/4},
\quad \log2\le u\le L,\quad c/3\le n\le c.
\tag{EB1}
$$

This comparison holds for every $c\ge10^{24}$. The integration begins
at $1/n\le\log2$, so the actual finite prefix is contained in the
proven range. These are explicit parameter calculations from a classical
equation and energy comparison for the required consumer, with no
claim of a new general Laguerre inequality.

### Finite low prefix using the existing global prime count

For every $c\ge10^{24}$, put $L=\log c>48$. Let
$w(t)=t^{-1/2}(\log t)^{-3/4}$ and
$g(t)=\sqrt t(\log t)^{-3/4}$. For $t\ge e^3$,
$g'(t)=(1/2-3/(4\log t))w(t)\ge w(t)/4$.
Also $w(2)<2$. The function $g$ increases on $[e^3,\infty)$, so
$g(c)\ge g(10^{24})>10^{12}/60>100$.
Thus

$$\int_2^c w(t)dt<54+4g(c)<5g(c). \tag{EB2}$$

The lower interval is bounded by $e^3w(2)<27\cdot2=54$.
Reuse Rosser--Schoenfeld Corollary1 eq(3.6), already owned in
[the existing Rosser--Schoenfeld entry](../Arith/rosser1962approximate.md): $\pi(x)<1.25506x/\log x$ for
$x>1$. It directly gives $\vartheta(x)\le\pi(x)\log x<2x$.
Stieltjes partial summation, with $\vartheta(2^-)=0$, gives

$$
\sum_{p\le c}\log p\,w(p)
\le2cw(c)+2\int_2^c t(-w'(t))dt
=4w(2)+2\int_2^c w(t)dt<11g(c).
$$

Monotonicity similarly gives
$\sum_{2\le m\le c}w(m)\le w(2)+\int_2^c w(t)dt<6g(c)$.
These are upper bounds on positive envelopes of the two ACTUAL finite
sums; no primary-prime cancellation is assumed. EB1 then gives for
all three actual indices

$$|q_n|=|Q_n(c)|\le200c^{3/4}L^{-3/4}. \tag{EB3}$$

The constant 200 rounds $10(11+6)=170$ outward. This replaces the
prime-subset-of-integers log loss by the already available global count;
no new prime-count theorem is derived.

### The unchanged remote cutoff has an explicit finite allowance

Use the complete CS24 formula with $N=c$, $U=\log X_c\ge c^4$.
Its existing constants satisfy
$C_\varepsilon=9.39+\kappa e^{d^2/2}+2e^{d^2/4}<22$,
$M=1.515<2$, $4/5<d=0.8274<1$ and $\kappa=1.42620<3/2$.
Together with $e<3$ these give
$\varepsilon(u)\le22u^M e^{-d\sqrt u}$.
For every $u\ge c^4$, monotonicity of $(\log u)/\sqrt u$ on $[e^2,\infty)$ gives

$$
\frac{(c+1)\log2+(c-1+M)\log u}{\sqrt u}
\le\frac{2(1+4\log c)}c<\frac{482}{10^{24}}<\frac25.
$$

The last comparison uses that $(1+4\log c)/c$ decreases for
$c\ge10^{24}$ and $\log(10^{24})<60$. Consequently the endpoint
and integrand in the owned CS24 are at most
$22e^{-2\sqrt u/5}$, and direct substitution into its displayed
integral bound gives

$$|r_n|=|Q_n-Q_n(X_c)|
\le22(14+5\sqrt U)e^{-2\sqrt U/5}<1. \tag{EB4}$$

For the last outward comparison put $z=\sqrt U\ge c^2\ge10^{48}$.
Since $14+5z\le6z$ and $\exp(2z/5)\ge(2z/5)^3/6$,
the bound is at most $12375/z^2<1$. No unknown asymptotic start,
prime enumeration, exponential evaluation or numerical experiment is
substituted for CS24. Every actual endpoint term remains.

The exact original CS28 relation and row sum now give

$$
\|K_j^{mid}-K_{a,b}\|_{op}
\le1000c^{3/4}(\log c)^{-3/4}+5
<c/16000+5,\qquad c\ge10^{24}. \tag{EB5}
$$

Here $c^{1/4}\ge10^6$ and $L^{3/4}>16$ because $48^3>16^4$.

### Pay the finite comparison with the same complete zero matrix

Now restrict $10^{24}\le c\le5\cdot10^{25}$.

Use the [exact Gram determinant/trace and reflected error](lagarias2007li.md#retain-a-uniformly-positive-gram-determinant)
in PTL3--PTL4 directly. For $\gamma>c$,
$\theta\ge\gamma/(\gamma^2+1)\ge5/(6\gamma)$, and
$\sin x\ge5x/6$ for $0\le x\le1/2$. Substitution into that exact formula and
$a\ge c/3$, $b\ge c/2$, $b^2+c^2\le2c^2$ gives

$$
\lambda_{min}(G_\rho)
\ge(5/6)^{10}\frac{c^4}{144\gamma^4}
>\frac{c^4}{1152\gamma^4}
>\frac{c^4}{1536\gamma^4}.
$$

Indeed $(5/6)^5=3125/7776>2/5$, so its tenth power exceeds $4/25>1/8$.
The existing radial row allowance is $2c^2/\gamma^4$, which is at most
$c^4/(6144\gamma^4)$ for $c^2\ge12288$. Hence the SAME complete tail
obeys $K^{tail}(c)\succeq c^4S_4^+(c)I/2048$.
Only this application's outward constants change; no standalone
constant-improvement result or repeated generic proof is retained.

The [finite whole-Li estimate](lagarias2007li.md)'s FV3--FV4 explicit
count and original annulus directly give

$$K^{tail}(c)\succeq\frac{N_+(2c)-N_+(c)}{32768}I
\succeq\frac{cL}{2^{19}}I
\succ\frac{3c}{32768}I. \tag{EB6}$$

This is a lower bound, not equality with an annulus. Keep FV6's exact
head(H0)+Gram-band+error-band+complete-tail decomposition,
$H_0=3\cdot10^{12}$. Its verified head and Gram band are positive
semidefinite, and FV8 gives
$\|E_{H_0,c}\|_{\rm op}<135c/(8\cdot10^8)<c/10^6$. Therefore

$$K_{a,b}\succeq(3/32768-10^{-6})cI. \tag{EB7}$$

All actual zeros, reflection partners and analytic multiplicities
remain in their original common-source pieces.

### Original arithmetic consumer and scope

Combining EB5--EB7 on the SAME actual original matrix gives

$$K_j^{mid}\succeq
[(3/32768-10^{-6}-1/16000)c-5]I
\succeq cI/50000. \tag{EB8}$$

For this rational comparison use $3/32768>9/100000$ and
$9/100000-10^{-6}-1/16000-1/50000=13/(2\cdot10^6)$;
the latter multiplied by $c$ exceeds $5$ at $c\ge10^{24}$.

EB5 is an effective approximation with the stated constants for every
adjacent positive Fibonacci triple $c\ge10^{24}$; its error is
$O(c^{3/4}(\log c)^{-3/4})$. EB8 additionally gives a finite sign for
the original arithmetic middle, with CS28's unchanged source, cutoffs
and full $h^*$. Cofinal positivity, an all-integer Robin interval beyond
the existing results, and RH remain unresolved.
