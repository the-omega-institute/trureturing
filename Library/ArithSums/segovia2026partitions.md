---
bibkey: segovia2026partitions
authors: Carlos Segovia
year: 2026
title: The Riemann Hypothesis through the looking of partitions
doi: null
url: https://arxiv.org/abs/2601.22413v4
claim: The preprint gives unconditional fixed-branch cutoff and actual-divisor-block asymptotics on superabundant integers; a growing finite progression window follows by applying its harmonic criterion and positive hook coefficients, without proving saturation or RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Espinosa branches and integer partitions

The source is Carlos Segovia, [arXiv:2601.22413v4](https://arxiv.org/abs/2601.22413v4),
version dated 16 October 2026. The inspected [primary PDF](https://arxiv.org/pdf/2601.22413v4)
has SHA-256 `0e01f8b760ea4c418769e643994d220e51ded7a62d00f0285d3a296b05a8be59`.
The locators below record inspected statements and their conditions;
they do not certify every proof or supply Lean verification.

The paper decomposes an Espinosa-type RH-equivalent inequality into
partition branches $A_r(n)$. Theorem 17 and Corollary 22 give unconditional
asymptotics for every fixed branch on actual superabundant integers.
Proposition 14 proves next-level progression for the first four branches
at every superabundant $N>5040$. Figure 1's finite calculation of the first
seven cutoffs on 10,000 computed colossally abundant integers retains the
Alaoglu--Erdős conjecture as a sequence-generation assumption; that
assumption is not used in Theorem 17's fixed-branch asymptotic statement.

The partition index $r$ counts a branch in a symmetric-polynomial
expansion. It is not a FIB five-window state, Fibonacci rank, or bound on
$\omega(N)$. The source gives no map from $[null,2,3,2\,5,5]$ to its
actual divisor subsets. Its actual-SA realization theorem can be reused
directly once a consumer's source satisfies those hypotheses; a FIB
application still needs its own common-source and observation interface.

## Actual cutoffs and fixed-branch realization

[Definition 10](https://arxiv.org/html/2601.22413v4#Thmthm10), (92)–(94),
uses a superabundant integer $N>5040$, ordered distinct divisors
$1=d_1<\cdots<d_{\tau(N)}=N$, branch weights $\rho_r>0$, and
$S_r=\sum_{k\le r}\rho_k\uparrow e^\gamma$. It defines

$$
j_r(N)=\max\left\{j:\sum_{i=1}^j\frac1{d_i}
                       \le S_r\log\log N\right\},
\qquad d^{(r)}(N)=d_{j_r(N)}.
$$

The cutoff is a divisor value; its index is $j_r$. Saturation means
$j_r=\tau(N)$, equivalently $Z(N)\le S_r\log\log N$ for
$Z(N)=\sigma(N)/N$. The defining prefix inequality does not bound the
omitted divisor tail or establish saturation.

Write $\varrho$ for the Dickman function, distinct from the coefficients
$\rho_r$, and $J(u)=\int_0^u\varrho(t)\,dt$. Definitions 15–16,
(111)–(116), specify $J(\alpha_r)=S_r$ and
$\int_0^\infty\varrho(t)\,dt=e^\gamma$.
[Theorem 17](https://arxiv.org/html/2601.22413v4#Thmthm17), (117)–(118), states

$$
d^{(r)}(N)\sim e^{-\gamma}(\log N)^{\alpha_r}
\qquad(N\to\infty\text{ through superabundant integers}),
$$

for every **fixed** $r\ge1$. It covers all sufficiently large SA integers
for that $r$, rather than just a chosen subsequence. The threshold may
depend on $r$. Corollary 21, (146)–(147), consequently gives
$d^{(r+1)}(N)/d^{(r)}(N)\to\infty$ for each fixed $r$.

The actual-source bridge is explicit. With $P$ the largest prime factor
of $N$, with $P(1)=1$, (110) defines

$$
F(x,y)=\sum_{\substack{m\le x\\P(m)\le y}}\frac1m,
\qquad F_N(x)=\sum_{\substack{d\mid N\\d\le x}}\frac1d.
$$

Lemma 18, (119), gives, uniformly on each fixed compact interval
$u\in[a,U]\subset(0,\infty)$,

$$
F(y^u,y)=\log y\,J(u)+\gamma\varrho(u)+O_{a,U}(1/\log y).
$$

Lemma 19, (129), retains the finite prime exponents of the same SA
integer and gives, for each fixed $U>0$, uniformly for $1\le x\le P^U$,

$$
0\le F(x,P)-F_N(x)\ll_U\frac{\log P}{\sqrt P}=o(1).
$$

Proposition 20, (136), combines these with $P\sim\log N$:
for fixed $s\in(0,e^\gamma)$ and $a>0$, with $J(\alpha)=s$,

$$
F_N(a(\log N)^\alpha)
=s\log\log N+\varrho(\alpha)(\log a+\gamma)+o(1).
$$

Its proof, (137)–(142), keeps the additional error
$(\alpha\varrho(\alpha)-s)(\log\log N-\log P)$ and
$O_{\alpha,a}(1/\log P+\log P/\sqrt P)$.
No numerical threshold or error uniform in growing $r$ is supplied by
these fixed-parameter statements. The inversion in Theorem 17 also uses
fixed $\varrho(\alpha_r)>0$.

## Realized blocks and rounding

[Corollary 22](https://arxiv.org/html/2601.22413v4#Thmthm22), (148)–(151),
sets $j_0=0$ and uses the actual reciprocal-divisor blocks

$$
\mathcal D_r(N)=\{N/d_j:j_{r-1}(N)<j\le j_r(N)\}.
$$

For each fixed $r$, on SA integers tending to infinity, it states

$$
\sum_{d\in\mathcal D_r(N)}d
=\rho_rN\log\log N+o(N)\sim A_r(N).
$$

The rounding estimate is already in the source, (150): whenever the
cutoff is unsaturated,

$$
0\le\varepsilon_r(N):=S_r\log\log N-
                 \sum_{i\le j_r(N)}\frac1{d_i}
 <\frac1{d_{j_r(N)+1}}\le\frac1{d^{(r)}(N)}.
$$

With $\varepsilon_0=0$, the exact block error in (151) is
$N(\varepsilon_{r-1}-\varepsilon_r)$. At $r=1$ it is nonpositive;
for $r\ge2$, (150) alone gives no sign for this difference.
The fixed-$r$ theorem makes the relevant cutoffs eventually unsaturated
and the errors $o(1)$. Prefix rounding, even when small, is distinct from
the complete omitted divisor tail.

## Progression criterion and a growing finite window

[Proposition 12](https://arxiv.org/html/2601.22413v4#Thmthm12), (95)–(99),
equates Robin on all SA $N>5040$ with progressive realizability:
for every such fixed $N$ and every unsaturated $r$, there must exist
$s>r$ with $j_s(N)>j_r(N)$. Finiteness of the divisor set then forces
saturation. This quantifier is stronger than progression of each fixed
branch only after a branch-dependent threshold in $N$.

[Lemma 13](https://arxiv.org/html/2601.22413v4#Thmthm13), (100)–(104),
gives a sufficient condition for progression at the very next level:
if some integer $m\ge1$ satisfies

$$
H_m\le S_r\log\log N,
\qquad \frac1{m+1}\le\rho_{r+1}\log\log N,
$$

then $j_r<\tau(N)$ implies $j_{r+1}\ge j_r+1$.
Proposition 14 proves these conditions for $r=1,2,3,4$ on every SA
$N>5040$. The conjecture immediately following it asks for next-level
progression at every unsaturated $r$ and every SA $N>5040$.

The following is an ordinary application of this criterion and the
source's positive hook formula, not a new general theorem or an
independent originality claim. Equation (84), also attributed to
[Gómez-Aíza](../Weil/gomezaiza2026younglattice.md), gives

$$
\rho_{r+1}\ge\widetilde\rho_{r+1}
=\frac1{(r+1)!}\sum_{m\ge1}\frac1{m^r(m+1)}
\ge\frac1{2(r+1)!}\qquad(r\ge1).
$$

Put $A=\log N$, $L=\log A$, and choose
$m=\lfloor\exp(S_rL-1)\rfloor$. Since $S_r\ge1$ and $N>5040$,
we have $m\ge1$. The elementary harmonic bound gives

$$
H_m\le1+\log m\le S_rL,
\qquad \frac1{m+1}<eA^{-S_r}.
$$

Consequently the explicit sufficient condition

$$
2e(r+1)!\le L A^{S_r}
$$

implies both hypotheses of Lemma 13 and hence next-level progression
whenever the current cutoff is unsaturated. This test uses the same
actual $N$ at both levels; it does not replace its divisors by all smooth
integers.

For every fixed $0<c<e^\gamma$, there is a threshold $N_c$ such that,
simultaneously for all SA $N\ge N_c$ and

$$
1\le r\le R(N):=\left\lfloor
 c\frac{\log\log N}{\log\log\log N}\right\rfloor,
$$

an unsaturated cutoff advances at $r+1$. To see this, choose fixed
$c<s<e^\gamma$ and $r_0$ with $S_{r_0}>s$. For
$r_0\le r\le R(N)$, as $L\to\infty$,

$$
\log\bigl(2e(r+1)!\bigr)
\le\log(2e)+(R(N)+1)\log(R(N)+1)
=(c+o(1))L<sL<S_rL+\log L.
$$

For the finitely many $r<r_0$, the same sufficient condition eventually
holds since $S_r>0$. This proves the asserted common threshold. In
particular, using only $S_r\ge1$ would not justify the part $1<c<e^\gamma$.
Lemma 13's footnote extends its argument to arbitrary integers
$N\ge5040$ if cutoffs are defined there; the same application then has
that broader domain. No SA asymptotic is needed for this progression test.

This controls a growing **finite** prefix. It neither proves saturation
for each fixed $N$ nor covers that integer's arbitrarily late branches.
It supplies no uniform fixed-branch asymptotic in that growing range,
no complete signed Robin margin, and no FIB-to-divisor source map.
The endpoint $c=e^\gamma$ and optimality of this window are not asserted.

## Additional reused inputs and the remaining Robin target

The [v3 PDF](https://arxiv.org/pdf/2601.22413v3), SHA-256
`8ce22ded9964d81c5742d39235f85f310be0ab013f637a946b3c5517db6cd239`,
contains a separate input used by the FIB full-stock analysis:
Lemma 8, pp.15–16, states that for each fixed $0<b<1$ there exists
$N_0(b)$ such that every SA $N>N_0(b)$ is divisible by
$\operatorname{lcm}(1,\ldots,\lfloor b\log N\rfloor)$.
This is an existential eventual statement, not an effective certificate
for one specified critical integer or a sequence of Robin global
maximizers. The v3 first-cutoff limit is included in v4 Theorem 17 at $r=1$.

The approximately 91.85% is the limiting total hook contribution relative
to $e^\gamma$, given in v4 Theorem 8 and (84)–(86). It is not a certified
fraction of $Z(N)$ at one integer. Equation (82)'s generating product and
(83)'s identity $\sum_r\rho_r=e^\gamma$ are literature inputs, not new
FIB or Robin estimates.

The remaining [Robin comparison](nicolas2025comparison.md) still requires
the complete joint signed bound at the same conditional extremal source.
The realized fixed branches and the growing progression window do not
provide that bound for the original zero head and price cost.
