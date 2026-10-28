---
bibkey: segovia2026partitions
authors: Carlos Segovia
year: 2026
title: The Riemann Hypothesis through the looking of partitions
doi: null
url: https://arxiv.org/abs/2601.22413v4
claim: The preprint gives unconditional fixed-branch SA realization; classical ultrafriable counts and reciprocal-tail estimates also yield a uniform actual-inventory tail interface, without controlling the signed Robin budget.
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

## Uniform tails from the ultrafriable comparison

The actual-inventory transfer can reuse a published counting theorem.
Tenenbaum, *On ultrafriable integers*, Quarterly Journal of Mathematics
**66** (2015), 333–351, DOI [10.1093/qmath/hau025](https://doi.org/10.1093/qmath/hau025),
Theorem 1.1, (1.10), compares ultrafriable and smooth counts. The inspected
[HAL v1 manuscript](https://hal.science/hal-01281588v1/document) has SHA-256
`ed4ef5bc5e26457e78ff99ac314bb8a70f33eafd8f94f62be619e176224a3578`.
Its missing-prime-power method is already in §3.1; no new sieve method
or originality claim is made here.

For the reciprocal tail use Tenenbaum, *Integers with a large friable
component*, Acta Arithmetica **124** (2006), 287–291, DOI
[10.4064/aa124-3-6](https://doi.org/10.4064/aa124-3-6).
The inspected [published PDF](https://www.impan.pl/shop/publication/transaction/download/product/83889?download.pdf)
has SHA-256 `999f2f0b2eea5a329f614c122e5916fe9633a38edee0cb7c53a0a2e996ab8b58`.
The following application keeps the same actual $N$; it is ordinary
mathematics, without Lean certification.

### Reused count and tail estimates

Put $\ell=\log P$, and distinguish the Dickman tail from the divisor
count by writing

$$
\mathcal T(u)=\int_u^\infty\varrho(t)\,dt,
\qquad
T(P,x)=\sum_{\substack{P^+(m)\le P\\m>x}}\frac1m,
\qquad T_N(x)=\sum_{\substack{d\mid N\\d>x}}\frac1d.
$$

For each fixed $0<\epsilon<3/5$, the 2006 formulas (1.2)–(1.3) state,
uniformly for $P\ge2$ and $1\le x\le\exp\exp(\ell^{3/5-\epsilon})$,
with $u=\log x/\ell$,

$$
T(P,x)=\ell\mathcal T(u)
 \left(1+O_\epsilon\!\left(\frac{\log(u+2)}\ell\right)\right).
$$

Lemma 2.1, (2.2), retains the next term:

$$
T(P,P^u)=\ell\mathcal T(u)-\gamma\varrho(u)
 +O_\epsilon\!\left(\frac{\varrho(u)\log(u+2)}\ell+P^{-u}\right).
$$

These are uniform source statements, including growing $u$. They need
no fixed-branch approximation from Segovia.

Write $\Psi(t,P)$ for the smooth count and $\Upsilon(t,P)$ for the
count of integers $m\le t$ in which every full prime-power factor is at
most $P$. The latter integers are exactly the divisors of
$C_P=\operatorname{lcm}(1,\ldots,\lfloor P\rfloor)$.
The 2015 theorem states, for each fixed $\eta>0$,

$$
\Upsilon(t,P)=\Psi(t,P)
 \left(1+O_\eta\!\left(\frac{v\log(2v)}{\sqrt P\,\ell}\right)\right),
\quad v=\frac{\log t}\ell,
\quad t\ge P\ge(\log t)^{2+\eta}.
$$

For SA $N$, initial prime support and the fact
$p^{v_p(N)+1}>P$ from Segovia's Lemma 19 give $C_P\mid N$. Thus

$$
\{d:d\mid C_P\}\subseteq\{d:d\mid N\}
 \subseteq\{m:P^+(m)\le P\}.
$$

This inclusion is the common-source bridge to the actual divisor
inventory. It does not identify the inventory with all smooth integers.

### Transfer by partial summation

Fix $a>0$ and $0<\epsilon<3/5$, and put

$$
U_P=\frac{\exp(\ell^{3/5-\epsilon})}\ell,
\qquad a\le u\le U_P,\qquad x=P^u,
\qquad X=P^{P^{1/4}}.
$$

Let $D(t)=\Psi(t,P)-\Upsilon(t,P)\ge0$. It vanishes for $t<P$.
Apply the 2015 theorem with fixed $\eta=1/4$. Throughout $P\le t\le X$
its domain holds for sufficiently large $P$, and its error gives
$D(t)\ll P^{-1/4}\Psi(t,P)$. By the inventory inclusion and partial
summation, retaining the nonpositive endpoint term $-D(x)/x$ as an
upper-bound omission,

$$
\begin{aligned}
0\le T(P,x)-T_N(x)
&\le\int_x^\infty\frac{D(t)}{t^2}\,dt-\frac{D(x)}x\\
&\le P^{-1/4}O\!\left(T(P,x)+\frac{\Psi(x,P)}x\right)
       +\int_X^\infty\frac{\Psi(t,P)}{t^2}\,dt.
\end{aligned}
$$

Here $x<X$ throughout the displayed range for sufficiently large $P$.
The 2006 formulas (2.3), (1.2) and the coarse comparison
$\mathcal T(u)\asymp\varrho(u)/\log(u+2)$ on $u\ge a$ give
$\Psi(x,P)/x\ll_a T(P,x)$. For $a\le u<1$ this also follows from
$\Psi(x,P)/x\le1$ and $T(P,x)\gg\ell$.

For the remaining integral, take $\sigma=1-1/\ell$. The classical
Rankin bound and the crude Euler-product bound
$\zeta(\sigma,P)=\prod_{p\le P}(1-p^{-\sigma})^{-1}\le P^C$ give

$$
\int_X^\infty\frac{\Psi(t,P)}{t^2}\,dt
 \le\ell e^{-P^{1/4}}\zeta(\sigma,P).
$$

The coarse Dickman lower bound recalled in the 2006 paper gives
$T(P,P^u)\ge\exp(-P^{o(1)})$ uniformly for $a\le u\le U_P$.
The last integral divided by that tail is therefore smaller than every
fixed negative power of $P$. Consequently the published count and tail
estimates imply the uniform actual-inventory transfer

$$
0\le1-\frac{T_N(P^u)}{T(P,P^u)}\ll_{a,\epsilon}P^{-1/4},
\qquad a\le u\le U_P.
$$

The exponent $1/4$ is only a sufficient choice in this application;
no optimality is asserted. More generally the same comparison applies
whenever $C_P\mid N$ and every prime factor of $N$ is at most $P$.

### An absolute inventory allowance on every tail

The same 2015 source supplies an absolute comparison at the additive
root scale. Fix $s>0$. For sufficiently large $P$ in terms of $s$, put
$\ell=\log P$, $\sigma=1-s/\ell$, and
$\nu_p=\lfloor\ell/\log p\rfloor$. Define the finite Euler factors

$$
\zeta(\sigma,P)=\prod_{p\le P}(1-p^{-\sigma})^{-1},\qquad
H_P(\sigma)=\prod_{p\le P}(1-p^{-(\nu_p+1)\sigma}).
$$

Their product is the ultrafriable Dirichlet polynomial in (1.3).
Lemma 2.3, (2.5)–(2.6), has the independent parameter domain
$1/\log P<\sigma\le2$ and gives

$$
V_P(\sigma):=
\sum_{p\le P}\frac{(\nu_p+1)\log p}{p^{(\nu_p+1)\sigma}-1}
\asymp
\frac{P^{1/2-\sigma}(1+P^{1/2-\sigma})\log P}
     {1+|1-2\sigma|\log P}.
$$

For example, $\ell\ge4(s+1)$ puts the chosen $\sigma$ in $[3/4,1)$
and in that source domain. Since $(\nu_p+1)\log p>\ell$, the
published bound directly gives

$$
\sum_{p\le P}p^{-(\nu_p+1)\sigma}
\le\frac{V_P(\sigma)}\ell
\ll_s\frac{P^{-1/2}}\ell.
$$

For the smooth factor, Lemma 2.2, (2.3)–(2.4), gives
$g_-(t,P)=\sum_{p\le P}\log p/(p^t-1)\ll_s\ell$ uniformly on
$\sigma\le t\le1$, with the removable value at $t=1$ understood.
Together with the classical Mertens product estimate this yields

$$
\zeta(\sigma,P)
=\zeta(1,P)\exp\!\left(\int_\sigma^1g_-(t,P)\,dt\right)
\ll_s\ell.
$$

For every $N$ with $C_P\mid N$ and $P^+(N)\le P$, the same actual
inventory inclusion and the Euler products therefore give

$$
\begin{aligned}
\sum_{\substack{P^+(m)\le P\\m\nmid N}}m^{-\sigma}
&\le\zeta(\sigma,P)[1-H_P(\sigma)]\\
&\le\zeta(\sigma,P)
       \sum_{p\le P}p^{-(\nu_p+1)\sigma}
\ll_sP^{-1/2}.
\end{aligned}
$$

For $m>P^u$, one has $m^{-1}\le e^{-su}m^{-\sigma}$. Rankin's
inequality consequently gives, uniformly for **all** $u\ge0$,

$$
\boxed{
0\le T(P,P^u)-T_N(P^u)\ll_sP^{-1/2}e^{-su}.}
$$

The threshold depends on the fixed $s$; no uniformity in $s$ or claim
for all small $P$ is asserted. This application uses the general
$\sigma$ lemma, not a substitution into (3.1)'s constrained
saddle-point parameter. It requires no smooth-tail asymptotic domain.
In particular, every $u(P)\to\infty$ gives an additive inventory error
$o(P^{-1/2})$. This is not a relative estimate for an arbitrarily small
tail, and does not by itself give $o(1/(\sqrt P\log P))$.

There is an actual growing-branch consumer. Let $N$ tend to infinity
through SA integers and let the integer-valued $r(N)\to\infty$.
The existing fixed-branch Theorem 17 and monotonicity of the cutoffs
already imply

$$
u_N:=\frac{\log d^{(r(N))}(N)}{\log P}\longrightarrow\infty.
$$

Indeed, $S_r\uparrow e^\gamma$ and strict increase of $J$ imply
$\alpha_r\to\infty$. For any fixed $M$, choose a fixed $r_0$ with
$\alpha_{r_0}>M$. Eventually $r(N)\ge r_0$, while Theorem 17 and
$P\sim\log N$ give
$\log d^{(r_0)}(N)/\log P\to\alpha_{r_0}>M$.
Applying the absolute bound at this actual cutoff gives

$$
T(P,d^{(r(N))}(N))-T_N(d^{(r(N))}(N))=o(P^{-1/2}).
$$

This includes saturated cutoffs and needs no upper bound on $u_N$.
For an unsaturated growing branch, the source's rounding estimate also
gives $0\le\varepsilon_{r(N)}(N)\le P^{-u_N}=o(P^{-1/2})$.
On unsaturated growing branches, inventory truncation and prefix
rounding are therefore negligible at this additive root scale. A sufficiently precise evaluation of the smooth
tail at the original cutoff and the sign of $Q_N$ are still needed;
neither follows from this allowance. These are applications of the
published Euler-factor estimates and fixed-branch theorem, not a new
sieve, growing-branch inversion, originality claim or Lean result.

### Density-scale precision and the remaining signed budget

The transfer error is small at the next-term scale:

$$
\frac{P^{-1/4}\ell\mathcal T(u)}{\varrho(u)}
 \ll_a\frac{P^{-1/4}\ell}{\log(u+2)}=o(1)
$$

uniformly in the displayed range. The same coarse Dickman lower bound
shows

$$
\frac{P^{-u}}{\varrho(u)}
 \le\exp\!\bigl(-u\ell+O_a(u\log(u+2))\bigr)=o(1).
$$

The 2006 formula (2.2) therefore gives

$$
T_N(P^u)=\ell\mathcal T(u)-\gamma\varrho(u)+o(\varrho(u)),
\qquad a\le u\le U_P,
$$

with a uniform remainder. For each fixed $c>0$, the classical derivative
estimate $|\varrho'(u)|\ll_a\varrho(u)\log(u+2)$ recalled before
Lemma 2.1 gives, by $u\mapsto u+\log c/\ell$,

$$
T_N(cP^u)=\ell\mathcal T(u)
 -(\log c+\gamma)\varrho(u)+o(\varrho(u)).
$$

Use the source parameter $\epsilon/2$ while keeping the displayed range
with $\epsilon$, so multiplication by fixed $c$ stays inside its domain.
The lower bound $a$ keeps the shifted argument positive.

In particular define the actual divisor quantile for this tail target by

$$
D_N(u)=\max\{d\mid N:T_N(d)\ge\ell\mathcal T(u)\}.
$$

For sufficiently large $P$ this set is nonempty and
$D_N(u)/(e^{-\gamma}P^u)\to1$ uniformly. Indeed, fix $t>0$ and use
$c=e^{-\gamma-t},e^{-\gamma-t/2},e^{-\gamma+t}$. The first two tails
exceed the target, and their difference is
$(t/2)\varrho(u)+o(\varrho(u))>0$, giving an actual divisor between
them. The third tail is below the target. This brackets the largest
admissible divisor by the same inversion used for fixed branches.

This is a specified tail quantile, distinct from the original branch's
prefix budget. For the latter put

$$
L=\log\log N,\quad\delta_N=L-\ell,\quad
Q_N=Z(N)-e^\gamma L.
$$

At an actual branch cutoff the exact relation is

$$
T_N(d^{(r)}(N))
 =\mathcal T(\alpha_r)L+Q_N+\varepsilon_r(N).
$$

Thus its target differs from $\ell\mathcal T(\alpha_r)$ by
$Q_N+\mathcal T(\alpha_r)\delta_N$, before rounding. The transfer does
not estimate this signed quantity, place an original growing-branch
cutoff in its domain, or determine the sign of $Q_N$. It supplies the
actual-inventory tail approximation from existing literature; the
signed Robin comparison and FIB-to-divisor map remain separate gaps.

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
