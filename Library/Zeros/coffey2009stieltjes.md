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
