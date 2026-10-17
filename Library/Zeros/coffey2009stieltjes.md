---
bibkey: coffey2009stieltjes
authors: Mark W. Coffey
year: 2009
title: The Stieltjes constants, their relation to the eta_j coefficients, and representation of the Hurwitz zeta function
doi: null
url: https://arxiv.org/abs/0706.0343v2
claim: Proposition 2(a) splits the Li arithmetic contribution into a Stieltjes term and an ordered von Mangoldt sum; the application supplies a sufficient subleading Stieltjes bound without importing Proposition 2(b).
strata_touched: []
license: citation-only
triage: anchor
---

# Stieltjes and prime-power parts of the Li joint estimate

The primary is Mark W. Coffey,
[arXiv:0706.0343v2](https://arxiv.org/abs/0706.0343v2), version
25 February 2009, first submitted in 2007. Source locators below refer
to that version. Proposition 2(a), equations (12), (14)--(17), supplies
the decomposition. The integral representation and sufficient weaker
bound below are applications of standard Euler--Maclaurin and Laguerre
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
false. Neither that bound nor the stronger Corollary 16 is used below.
A weaker estimate suffices for the joint leading scale, and can be
obtained with absolute values throughout.

## CS3. A sufficient absolute estimate from standard orthogonality

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
Set $p_n=L_{n-1}^{(2)}$. Telescoping the same contiguous identity gives

$$
p_n=\sum_{k=0}^{n-1}L_k^{(1)}
   =\sum_{k=0}^{n-1}(n-k)L_k^{(0)}.
$$

The Laguerre row of
[DLMF Table 18.3.1](https://dlmf.nist.gov/18.3.T1) has weight
$u^\alpha e^{-u}$ and squared norm $\Gamma(k+\alpha+1)/k!$,
for $\alpha>-1$. Its cases $\alpha=1$ and $\alpha=0$ give exactly

$$
A_n:=\int_0^\infty ue^{-u}p_n(u)^2\,du=\frac{n(n+1)}2,
\qquad
B_n:=\int_0^\infty e^{-u}p_n(u)^2\,du
 =\frac{n(n+1)(2n+1)}6.
\tag{CS6}
$$

Weighted Cauchy--Schwarz, without dropping any sign changes, gives

$$
\int_0^\infty e^{-u}|p_n(u)|\,du
\le\left[(A_n+B_n/n)
 \int_0^\infty\frac{e^{-u}}{u+1/n}\,du\right]^{1/2}.
$$

Splitting the last integral at one bounds it by $\log(n+1)+1$.
Since $|P_1|\le1/2$, CS5 proves the explicit sufficient bound

$$
|S_\gamma(n)|\le\frac n2+
 \frac12\sqrt{(A_n+B_n/n)(\log(n+1)+1)},
$$

and hence, unconditionally,

$$
\boxed{S_\gamma(n),\ U_n=O(n\sqrt{\log(n+1)})=o(n\log n).}
\tag{CS7}
$$

This does not validate the source's stronger $O(n)$ claim. It controls
one component of CS3, with the entire signed $P_n$ still present.

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
D_j=ab(\log b)^2+O\bigl(b^2(\log b)^{3/2}\bigr),
\qquad
2(h_b+h_c)=(b+c)\log b+O\bigl(b\sqrt{\log b}\bigr).
\tag{CS11}
$$

Indeed $h_t=\tfrac12t\log b+O(b\sqrt{\log b})$ for
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
