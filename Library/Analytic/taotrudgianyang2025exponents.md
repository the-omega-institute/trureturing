---
bibkey: taotrudgianyang2025exponents
authors: Terence Tao, Tim Trudgian and Andrew Yang
year: 2025
title: "New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach"
doi: null
url: https://arxiv.org/abs/2501.16779v1
claim: Theorem 51 supplies an unconditional density bound that controls the actual cumulative zero response and its coefficient-preserving horizontal subtraction on the band 17/22 <= Re(rho) <= 79/100 above height X^(14/125). The complementary signed Robin budget remains unproved.
strata_touched: []
license: citation-only
triage: anchor
---

# A higher horizontal band of the actual cumulative response

The primary source is Tao–Trudgian–Yang,
[arXiv:2501.16779v1](https://arxiv.org/abs/2501.16779v1), submitted
28 January 2025, with [versioned PDF](https://arxiv.org/pdf/2501.16779v1).
Definition 37, Theorem 51 and Table 2 were checked in the primary text.
The source theorem is reused; the application below is a paper derivation,
not an originality claim or a complete Lean verification.

## The density input and its range

Definition 37, printed p.22, defines $N(\sigma,T)$ as the count of zeta zeros
with $\operatorname{Re}\rho\ge\sigma$ and $|\operatorname{Im}\rho|\le T$.
Its definition of $A(\sigma)$ uses an infinitesimal left shift in $\sigma$;
in particular it supplies

$$
N(\sigma,T)\ll_{\sigma,\eta}
T^{A(\sigma)(1-\sigma)+\eta}
\qquad(\eta>0)
$$

at each fixed $1/2\le\sigma<1$. The actual zero multiplicities are retained.

Theorem 51, printed p.29, unconditionally gives

$$
A(\sigma)\le
\max\left\{\frac{2}{9\sigma-6},
\frac{9}{8(2\sigma-1)}\right\},
\qquad \frac{17}{22}\le\sigma\le\frac45.
\tag{1}
$$

The density hypothesis named in the theorem's title is not an assumption.
The constants in the resulting density bounds need not be uniform in
$\sigma$; the application uses only finitely many fixed bins.

Table 2, printed p.33, lists stronger classical inputs near $\sigma=4/5$.
In particular its $A(\sigma)\le3/(2\sigma)$ row has the same endpoint value
$15/8$ as (1). Thus that endpoint alone cannot establish an improvement
over the literature. The application instead uses the endpoint $79/100$,
where the table lists Theorem 51, and compares only the specified prior
inputs below. No claim against every other density estimate is made.

## Preserve the actual integral and its coefficient

Reuse the actual cumulative response and integral-kernel estimate from
[the Guth–Maynard note](guthmaynard2024largevalues.md), equations (5)–(8).
For $X\ge A_0\ge50$, put $a=\log A_0$, $L=\log X$ and

$$
\begin{aligned}
\mathcal H_X(z)
&=\int_a^L t e^{t/2}
\left[\int_t^\infty
 e^{-(1-z)u}\frac{u+1}{u^2}\,du\right]dt,\\
s_\rho(X)&=-\frac{\mathcal H_X(\rho)}\rho.
\end{aligned}
\tag{2}
$$

For an actual zero $\rho=\beta+i\gamma$, define
$\rho^\circ=1/2+i\gamma$. This projected parameter is not asserted to be
an actual zero. The subtraction preserving the coefficient $-1/\rho$ is

$$
d_\rho(X)=-\frac{
\mathcal H_X(\rho)-\mathcal H_X(\rho^\circ)}\rho.
\tag{3}
$$

All appearances of $\mathcal H_X$ retain the same lower boundary,
the actual upper cutoff and the infinite inner tail. Replacing the
coefficient by $-1/\rho^\circ$ would introduce a separate correction and
is not the projection in (3). These projected integrals are also not the
already formalized cosine phase cost of the ordinate-stiffness theorem.

The existing kernel estimate applies to every parameter in the strip,
so it also applies at $\rho^\circ$. For $|\gamma|\ge1$ it gives

$$
|s_\rho(X)|\le
\frac{3X^{\max(\beta-1/2,0)}}{|\gamma|^3},
\qquad
|\mathcal H_X(\rho^\circ)|
\ll_{A_0}|\gamma|^{-2}.
\tag{4}
$$

Since $|\rho|\ge|\gamma|$, (3) and (4) imply
$|d_\rho(X)|\le|s_\rho(X)|+O_{A_0}(|\gamma|^{-3})$.
This reuses the kernel estimate, rather than proving a new oscillatory
integral formula or discarding the coefficient dependence on $\beta$.

## A cutoff that the selected prior inputs do not pay

Let $h=14/125$, $b=79/100$ and select the actual zero multiset

$$
\mathcal R_X=
\left\{\rho=\beta+i\gamma:
\frac{17}{22}\le\beta\le b,
\quad |\gamma|>X^h\right\}.
\tag{5}
$$

Conjugates and multiplicities are included. For every fixed
$\varepsilon>0$, the application of (1) and (4) gives

$$
\sum_{\rho\in\mathcal R_X}
\bigl(|s_\rho(X)|+|d_\rho(X)|\bigr)
\ll_{\varepsilon,A_0}
X^{-11/29000+\varepsilon}.
\tag{6}
$$

Here is the parameter mapping. Set

$$
B(\sigma)=(1-\sigma)
\max\left\{\frac{2}{9\sigma-6},
\frac{9}{8(2\sigma-1)}\right\},
\qquad
f(\sigma)=\sigma-\frac12+h[B(\sigma)-3].
\tag{7}
$$

For a fixed bin $[\sigma,\sigma+q]$ inside the band and a dyadic height
interval $[T,2T]$, (1) and (4) bound its contribution by
$O_{\sigma,\eta,A_0}(X^{\sigma+q-1/2}T^{B(\sigma)-3+\eta})$.
Summing heights from $X^h$ to infinity yields the exponent
$f(\sigma)+q+h\eta$. A finite mesh with sufficiently small fixed $q,\eta$
absorbs this loss into $\varepsilon$. No uniform density constant over
a continuum of $\sigma$ is assumed.

The derivatives of the two branches of $f$ are

$$
1-\frac{6h}{(9\sigma-6)^2},
\qquad
1-\frac{9h}{8(2\sigma-1)^2}.
$$

Their lower bounds at $17/22$ are respectively $689/2625$ and
$1153/2000$, both positive. Thus both branches increase on the band.
At $b$, the two density powers are $14/37$ and $189/464$; the two
response exponents are $-67/18500$ and $-11/29000$.
Their maximum gives (6). The sums in (6) are absolutely convergent;
the actual kernel and zero count justify the infinite height tail.

For comparison, the older Bourgain bound $A(\sigma)\le2$ for
$\sigma>25/32$ is recalled on printed p.29. The Guth–Maynard bound
$A(\sigma)\le15/(3+5\sigma)$ is Theorem 49 on printed p.28 and is
already used in the project. At the same endpoint and cutoff, the
three allowances are

| Density input at $b=79/100$ | $b-1/2+h[B(b)-3]$ |
| --- | --- |
| Theorem 51 | $-11/29000$ |
| Bourgain's stated $A\le2$ input | $13/12500$ |
| Guth–Maynard's stated input | $331/69500$ |

These positive numbers are allowances in upper estimates, not lower
bounds for the actual contribution. The comparison is with these
specific inputs and does not assert a new density theorem or a
globally optimal height cutoff. For $0<\varepsilon<11/29000$, (6)
controls this part of the response and its horizontal subtraction by
$o(1)$ at every sufficiently large real $X$.

## The unpaid contribution

The band in (5) lies to the right of the previously controlled
$1/2<\beta\le3/4$ sector. It leaves the remaining horizontal bands and
the part below its moving height uncontrolled. Every fixed off-line
zero eventually lies below that height; its growing mode is not removed
by this estimate.

No bound here pays the joint sign of the complementary contribution,
produces a fixed lower budget for the full actual cumulative response,
or proves RH or Robin's inequality for every integer above 5040.
The density input and integral-kernel transport remain paper inputs
without a complete Lean implementation of (6).
