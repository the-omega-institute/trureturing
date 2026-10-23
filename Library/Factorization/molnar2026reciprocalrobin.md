---
bibkey: molnar2026reciprocalrobin
authors: Grant Molnar
year: 2026
title: Reciprocal LCM powers and Robin's criterion
doi: null
url: https://arxiv.org/abs/2610.12816v1
claim: "The reciprocal LCM-power function is the existing increment source b_kappa. The preprint reports an RH-equivalent unbounded-parameter criterion and unconditional normalized inequalities for all n > 5040 at 1 < kappa <= 100000; a bounded parameter interval does not settle classical Robin."
strata_touched: []
license: citation-only
triage: anchor
---

# Reciprocal LCM powers: reuse the existing source and parameter criterion

The inspected primary is [arXiv:2610.12816v1](https://arxiv.org/pdf/2610.12816v1),
submitted 8 October 2026, 23 pages. The definitions, theorem statements,
parameter-criterion argument and certification description cited below were
read in that version. The full analytic proofs and computer certificates
have not been independently verified or Lean compiled here. These results
belong to Molnar. The project applications below combine the cited local
power-mean formula with classical CA structure and Robin bounds; they are
paper-level deductions, not new source theorems or Lean-certified results.
No originality or peer-review claim is made.

## The reciprocal object already occurs in the project

With $Z(n)=\sigma(n)/n$, Definition 1.2 and equations (5)--(7), printed
pp.1--2, give

$$
\sigma_{-1}^{[\kappa]}(n)
=\sum_{d\mid n}\mu(d)Z(n/d)^\kappa=b_\kappa(n),
\qquad
Z(n)^\kappa=\sum_{d\mid n}b_\kappa(d).
$$

This is the same increment source identified in the
[Fan--Kobayashi--Molnar note](../ArithSums/fankobayashimolnar2025family.md).
Its local factor is $Z(p^a)^\kappa-Z(p^{a-1})^\kappa$.
For integral $k$, equation (8), printed p.2, already supplies

$$
b_k(n)=\sum_{\operatorname{lcm}(d_1,\ldots,d_k)=n}
\frac1{d_1\cdots d_k}.
$$

Reproving this expansion or introducing the same source under a FIB
name would duplicate existing work. The distinct nonreciprocal function
$\sigma^{[\kappa]}$ in the earlier paper must not be substituted for it.

Theorem 2.8, printed pp.6--8, supplies complete Selberg--Delange
expansions for both $\sum_{n\le x}n b_\kappa(n)$ and
$\sum_{n\le x}b_\kappa(n)$ at each fixed real $\kappa>1$.
This is a directly citable weighted expansion for the corrected
Balakrishnan--Pétermann input discussed in the earlier note.
Its $\kappa$-dependent errors do not pay the project's required
growing-parameter error at $s=y\log y$.

## Normalize before applying the Robin criterion

Definition 1.4, printed p.2, uses

$$
\widehat\rho^{[\kappa]}(n)
=\left(\frac{n b_\kappa(n)}{\kappa^{\omega(n)}}\right)^{1/(\kappa-1)},
\qquad \kappa>1,
$$

where $\omega(n)$ counts distinct prime divisors. This normalization is
part of the tested function, not an optional factor in its budget.
Lemma 3.1 and equation (53), printed p.13, state that for every fixed
integer $n>1$,

$$
\widehat\rho^{[\kappa]}(n)<Z(n),
\qquad
\widehat\rho^{[\kappa]}(n)\nearrow Z(n)
\quad(\kappa\to\infty).
$$

Theorem 3.4, printed p.14, states that for any fixed unbounded set
$\mathcal K\subset(1,\infty)$, RH is equivalent to

$$
\widehat\rho^{[\kappa]}(n)<e^\gamma\log\log n
\quad\text{for every integer }n>5040
\text{ and every }\kappa\in\mathcal K.
$$

The same theorem allows a common eventual integer cutoff for all
$\kappa\in\mathcal K$. Its reverse implication uses Robin's strict
violations under RH failure; passing a strict inequality to a limit
alone would yield only a weak inequality and is not its proof.

## The bounded-parameter theorem is unconditional

Theorem 4.7, printed pp.18--19, reports an explicit finite cutoff
$N_{\kappa_0}$ for every real $\kappa_0>1$, beyond which the normalized
inequality holds for every real $1<\kappa\le\kappa_0$.
Theorem 4.9, printed p.20, reports the stronger complete range

$$
\widehat\rho^{[\kappa]}(n)<e^\gamma\log\log n
\quad(n>5040,\ 1<\kappa\le100000).
$$

This is an all-integer statement for a bounded interval of the
reciprocal parameter. It is not a new finite verification of the
classical function $Z(n)$, nor a result for unbounded $\kappa$.
The source combines an analytic endpoint-transfer theorem with
directed interval certificates; its code and certification section,
printed p.22, names the MIT-licensed
[reciprocal-robin repository](https://github.com/grantmolnar/reciprocal-robin).
Those certificates have not been rerun here.

Corollary 4.8, printed p.19, already states that along any sequence of
strict classical Robin violations tending to infinity, the reciprocal
parameter at which each violation becomes visible must tend to
infinity. Thus increasing a finite parameter ceiling alone does not
exclude such a sequence.

## Project application: quantify loss on the same integer

Write $Q_\kappa(n)=\widehat\rho^{[\kappa]}(n)$ and
$B(n)=e^\gamma\log\log n$. For $n>5040$, define

$$
D_\kappa(n)=\log Z(n)-\log Q_\kappa(n)>0.
$$

For each actual factor $p^a\parallel n$, put $s=\sigma(p^a)$,
$u=1-1/s$ and $r=\kappa-1>0$. Equation (53) directly supplies

$$
\begin{aligned}
d_\kappa(p^a)
&=-\frac1r\log\left(\frac{s(1-u^\kappa)}\kappa\right),\\
D_\kappa(n)&=\sum_{p^a\parallel n}d_\kappa(p^a).
\end{aligned}
\tag{L1}
$$

The exact signed account is consequently

$$
\log\frac{B(n)}{Z(n)}
=\log\frac{B(n)}{Q_\kappa(n)}-D_\kappa(n).
\tag{L2}
$$

Thus a positive normalized margin pays the classical Robin budget only
when it also exceeds this loss on the same integer. Neither a separate
extremizer nor the limit at a different integer can replace it.

Two elementary estimates of the source's power mean are useful. Since
$u^\kappa\le u$, its mean $A=s(1-u^\kappa)/\kappa$ satisfies
$1/\kappa\le A<1$. Therefore

$$
0<D_\kappa(n)\le
\omega(n)\frac{\log\kappa}{\kappa-1}.
\tag{L3}
$$

For a lower bound, the integral in (53) gives

$$
A=s\int_u^1t^r\,dt
\le\frac{1-e^{-r/s}}{r/s}
\le\frac1{1+r/(2s)}.
$$

The first inequality uses $\log t\le t-1$. For the second, the function
$x-(1+x/2)(1-e^{-x})$ vanishes at zero and has derivative
$[1-(1+x)e^{-x}]/2\ge0$ for $x\ge0$.
Using $\log(1+y)\ge y/(1+y)$ then yields

$$
d_\kappa(p^a)\ge
\frac{\log(1+r/(2s))}{r}
\ge\frac1{2s+r},\qquad \kappa>1.
\tag{L4}
$$

These bounds are applications of (53), including for $1<\kappa<2$;
they do not supply a new power-mean theorem.

## Classical CA visibility requires a superlinear parameter

Here CA has its classical meaning: for some $\epsilon>0$, the actual
integer $n$ maximizes $Z(m)m^{-\epsilon}$ over positive integers $m$.
Reuse the [classical initial-prime support](../Arith/alaoglu1944highly.md)
and [CNS v2 equations (9), (11) and Lemma 1, printed pp.8--9](../Arith/caveney2012sacaga.md).
Equation (11) includes every maximizing tie, not only the largest
maximizer at each price. Put

$$
P=P^+(n)\ge37,\qquad M(n)=\#\{p:v_p(n)=1\}.
$$

With $q$ the next prime after $P$, the weak maximizing comparisons give
$F(q,1)\le\epsilon\le F(P,1)$ in the source's notation. Thus its
threshold $x_1$ satisfies $P\le x_1\le q<2P$, using Bertrand's bound.
The published Lemma 1 gives $x_2<\sqrt{2x_1}<2\sqrt P$; equation (9)
therefore puts every prime of actual exponent at least two below
$2\sqrt P$. Consequently

$$
\pi(P)-\pi(2\sqrt P)\le M(n)\le\pi(P),
\qquad M(n)\sim\frac P{\log P}\quad(P\to\infty).
$$

The thresholds and weak comparisons preserve all ties. Applying (L4)
to these actual exponent-one factors, with $s=p+1\le P+1$, gives

$$
D_\kappa(n)\ge\frac{M(n)}{\kappa+2P+1}.
\tag{V1}
$$

For any fixed $C>0$, a parameter $1<\kappa\le CP$ therefore loses at
least $M(n)/((C+2)P+1)\sim1/[(C+2)\log P]$ as $P\to\infty$.

Now additionally suppose $n>5040$ is a strict classical Robin violation.
As in the source's Corollary 4.8, set

$$
\kappa^\dagger(n)=
\inf\{\kappa>1:Q_\kappa(n)\ge B(n)\}.
$$

This set is nonempty because $Q_\kappa(n)\nearrow Z(n)>B(n)$.
Reuse [Robin's unconditional envelope, as recalled in CNS equation (2)
and printed p.15](../Arith/caveney2012sacaga.md), in the form

$$
\log\frac{Z(n)}{B(n)}
<\frac{K_R}{(\log\log n)^2},\qquad
K_R=0.6483e^{-\gamma}.
$$

For every parameter in the defining set, (L2) gives
$D_\kappa(n)\le\log(Z(n)/B(n))$. Combining this with (V1) and then
taking the infimum, without assuming it is attained, gives

$$
\kappa^\dagger(n)\ge
\frac{e^\gamma}{0.6483}M(n)(\log\log n)^2-2P-1.
\tag{V2}
$$

A second use of the same local formula improves this scale. Put
$L=\log\log n$, $T=M(n)L^2/K_R$ and $R=T-2P-1$.
Suppose $R>P+1$. Since $A=s(1-u^\kappa)/\kappa\le s/\kappa$,
every visible parameter satisfies $\kappa>R$ and

$$
D_\kappa(n)\ge
\frac{M(n)}{\kappa-1}\log\frac{\kappa}{P+1}
\ge\frac{M(n)}{\kappa-1}\log\frac{R}{P+1}.
$$

The exponent-one terms have $s=p+1\le P+1$; the omitted local losses are
nonnegative. Combining with the same envelope and taking the infimum gives

$$
\kappa^\dagger(n)\ge1+T\log\frac{R}{P+1},\qquad R>P+1.
\tag{V3}
$$

Along any sequence of classical CA violations tending to infinity,
$P\to\infty$: bounded $P$ bounds the optimizing price below by the
next-prime comparison, which bounds each occupied exponent above.
Initial prime support gives $\vartheta(P)\le\log n$. The prime number
theorem therefore gives $L\ge\log P+o(1)$ and
$M(n)\sim P/\log P$. Thus
$T\ge(1+o(1))P\log P/K_R$ and
$\log(R/(P+1))\ge\log\log P-\log K_R+o(1)$;
in particular $R>P+1$ eventually. It follows that

$$
\liminf_{\substack{n\to\infty\\n\text{ classical CA violation}}}
\frac{\kappa^\dagger(n)}
{P^+(n)\log P^+(n)\log\log P^+(n)}
\ge\frac{e^\gamma}{0.6483}.
\tag{V4}
$$

The assertion is conditional on such a sequence; it does not assert the
existence of a violation. This quantitative application strengthens the
qualitative parameter-escape conclusion for classical CA witnesses.
It does not transfer the classical CA structure to normalized reciprocal
maximizers.

## What the explicit cutoff already supplies for growing parameters

The explicit cutoff in Theorem 4.7, equations (66)--(72), can be used
before asking for another uniform estimate. Write

$$
A_\kappa=\frac{3(\kappa+3)}4,\qquad C_\kappa=\vartheta(A_\kappa),
$$

$$
X_\kappa=\max\!\left\{2278382,\frac{100}{31}
\left(C_\kappa+\frac13\right)\right\},
\qquad q_\kappa=\min\{p\text{ prime}:p>X_\kappa\}.
$$

These are the source's constants. Its admissible cutoff is

$$
N_\kappa^{\mathrm{eff}}=
\left\lceil\exp\!\left(
\frac{\log\prod_{p\le q_\kappa}(1-p^{-1})^{-1}\,\log q_\kappa}
{\log Q_\kappa(q_\kappa)}\right)\right\rceil.
\tag{U1}
$$

Put $a=31/75$ and $h=\log((e^a-1)/a)>0$.
The prime number theorem gives $q_\kappa\sim(75/31)\kappa$.
For this exponent-one factor the source's local formula reads

$$
Q_\kappa(q_\kappa)^{\kappa-1}
=\frac{(1+1/q_\kappa)^\kappa-1}{\kappa/q_\kappa}
\longrightarrow\frac{e^a-1}{a}.
$$

Thus $\log Q_\kappa(q_\kappa)\sim h/\kappa$. The unconditional
Mertens product asymptotic in (U1) consequently gives

$$
\log N_\kappa^{\mathrm{eff}}
\sim\frac{\kappa\log\kappa\log\log\kappa}{h}
\qquad(\kappa\to\infty).
\tag{U2}
$$

The source also supplies the earlier actual endpoint

$$
\epsilon_\kappa=\max_{a\ge1}
\frac{\log Q_\kappa(q_\kappa^a)}{a\log q_\kappa},
\qquad E_\kappa=\mathcal N_\kappa(\epsilon_\kappa),
$$

with largest-at-a-tie convention. Theorem 4.7 proves the normalized
inequality for all $n\ge E_\kappa$ and all real parameters in
$(1,\kappa]$. Its proof bounds $E_\kappa$ by comparing each occupied
exponent with zero. Comparing with the preceding exponent instead
controls the high layers of this same normalized endpoint.

For an actual $p^a\parallel E_\kappa$ with $a\ge2$, put
$Z_a=Z(p^a)$. The power-mean interval in (53) gives
$Z_{a-1}<Q_\kappa(p^a)<Z_a$. Local maximality, including ties, therefore
gives

$$
\begin{aligned}
\epsilon_\kappa\log p
&\le\log\frac{Q_\kappa(p^a)}{Q_\kappa(p^{a-1})}
<\log\frac{Z_a}{Z_{a-2}}\\
&=\log\left(1+\frac{p^{-(a-1)}+p^{-a}}{Z_{a-2}}\right)
\le\frac{3}{2p^{a-1}}.
\end{aligned}
\tag{U3}
$$

Define the explicit bound

$$
Y_\kappa=\max\!\left\{2,
\frac{3\log q_\kappa}{2\log2\,\log Q_\kappa(q_\kappa)}\right\}.
$$

Since $\epsilon_\kappa\ge\log Q_\kappa(q_\kappa)/\log q_\kappa$,
(U3) implies $p^{a-1}\le Y_\kappa$. Thus $a\ge3$ requires
$p\le\sqrt{Y_\kappa}$, and each contribution above the first two layers
is at most $\log Y_\kappa$. Consequently

$$
\log E_\kappa\le
2\vartheta(q_\kappa)+\pi(\sqrt{Y_\kappa})\log Y_\kappa.
\tag{U4}
$$

The first two layers are overcounted by $2\vartheta(q_\kappa)$;
no classical CA exponent rule has been applied to these normalized
maximizers. In particular the ceiling of the exponential of the
right-hand side of (U4) is another admissible cutoff, by the source's
endpoint theorem.

The exponent-one asymptotic above gives
$Y_\kappa=O(\kappa\log\kappa)$. Even the elementary bound
$\pi(t)\le t$ makes the tail in (U4) $o(\kappa)$. Hence

$$
\limsup_{\kappa\to\infty}\frac{\log E_\kappa}{\kappa}
\le\frac{150}{31}.
\tag{U5}
$$

For every fixed $0<c<31/150$, set
$j_c(n)=\lceil c\log n\rceil$. Equation (U5) implies
$\log E_{j_c(n)}/\log n\le(150/31)c+o(1)<1$ eventually. Applying
the source's endpoint theorem at this same parameter yields

$$
Q_\kappa(n)<B(n)
\quad\text{for every }n\ge n_0(c)
\text{ and every real }1<\kappa\le j_c(n).
\tag{U6}
$$

No numerical value of $n_0(c)$ or optimality of $31/150$ is claimed.
The boundary $c=31/150$ is unsettled by this bound. This application
uses the actual endpoint theorem and a uniform high-layer bound;
it does not exchange the quantifiers of a fixed-parameter eventual
statement. Equations (U3)--(U6) are project deductions from the cited
source, not a quoted source theorem, an originality claim, or a new
estimate for classical $Z(n)$.

## A single predetermined growing parameter

For every integer $n>5040$, choose

$$
k(n)=\left\lceil(\log n)^{3/2}\right\rceil.
\tag{D1}
$$

Writing $X=\log n$, the elementary bound
$\omega(n)\le X/\log2$ and (L3) give, uniformly over these integers,

$$
D_{k(n)}(n)
=O\!\left(\frac{\log X}{\sqrt X}\right)
=o(X^{-b})\quad\text{for every fixed }0<b<1/2.
\tag{D2}
$$

The relevant quantitative input is the [CNS v2 oscillation on printed
p.15](../Arith/caveney2012sacaga.md), citing Robin 1983, [15], p.241,
not just Molnar's qualitative Theorem 3.4. Under RH failure it supplies
fixed $0<b<1/2$ and $c>0$ and arbitrarily large actual CA integers with

$$
\frac{Z(n)}{B(n)}>1+c(\log n)^{-b}.
$$

For these same integers the logarithm of the ratio eventually exceeds
$(c/2)X^{-b}$. By (L2) and (D2), they then satisfy
$Q_{k(n)}(n)>B(n)$. Conversely RH implies $Q_{k(n)}(n)<Z(n)<B(n)$ for
every $n>5040$. This proves at the paper-application level

$$
\begin{aligned}
\mathrm{RH}
&\iff Q_{k(n)}(n)<B(n)\quad\text{for every integer }n>5040\\
&\iff Q_{k(n)}(n)<B(n)\quad\text{for all sufficiently large integers }n.
\end{aligned}
\tag{D3}
$$

This selects one parameter per integer instead of testing every parameter
at every integer. It does not establish the sign of that single test.
The source's Theorem 4.9 already settles (D1)'s test on the entire range
$5040<n\le\exp(100000^{2/3})$, by direct substitution since
$k(n)\le100000$ there. No new integer enumeration is needed for this
normalized initial range; it is not a new verified range for $Z(n)$.
The bounded theorem does not cover the remaining unbounded schedule.
Nor does (U6): its certified parameter is linear in $\log n$,
whereas (D1) grows as $(\log n)^{3/2}$. For the source's original
explicit cutoff, (U2) also gives
$\log N_{k(n)}^{\mathrm{eff}}/\log n\to\infty$.
Neither estimate certifies (D3); this insufficiency does not refute
the diagonal inequality.
The loss, CA-visibility and diagonal arguments above were not located in the
inspected Molnar v1 statement; they are
recorded here as combined applications of existing inputs, without a
priority or Lean-verification claim.

## A joint deficit on the original integer

The following application combines the same local loss with the classical
CA supporting price. Its purpose is to control each actual integer,
including integers whose prime support or exponents differ from a CA
maximizer. The supporting identity is bookkeeping; the estimate below
charges all three possible exponent choices on a prime band.

For $X=\log n>2$ and $L=\log X$, put

$$
\epsilon_X=\frac{\log(1+1/X)}{\log X},\qquad
F_{X,p}(a)=\log Z(p^a)-\epsilon_Xa\log p
\quad(a\in\mathbb Z_{\ge0}).
$$

Let $N_X$ be the largest classical CA maximizer at this price. Define

$$
S_{X,p}(a)=\max_{j\in\mathbb Z_{\ge0}}F_{X,p}(j)-F_{X,p}(a)\ge0,
\qquad d_\kappa(p^0)=0,
$$

$$
J_\kappa(n)=\sum_p
\left(S_{X,p}(v_p(n))+d_\kappa(p^{v_p(n)})\right).
\tag{J1}
$$

The sum is finite: outside the supports of $n$ and $N_X$, both terms
vanish. These are deficits of the original integer, not losses taken
from a different normalized maximizer. Multiplicativity gives exactly

$$
\log\frac{Q_\kappa(n)}{B(n)}=H_X-J_\kappa(n),\qquad
H_X=\log Z(N_X)+\epsilon_X(X-\log N_X)-\gamma-\log L.
\tag{J2}
$$

The [CNS classical CA thresholds](../Arith/caveney2012sacaga.md),
equations (7)--(11) and Lemma 1, give
$\log N_X\ge\vartheta(X)$, support on primes at most $X$, and optimal
exponent one whenever $\sqrt{2X}<p<X$. Choosing the largest maximizer
includes the first-layer tie if $X$ itself is prime. With
$\mathcal M(X)=\prod_{p\le X}(1-p^{-1})^{-1}$, it follows that

$$
H_X\le E(X):=
\log\mathcal M(X)-\gamma-\log L
+\epsilon_X(X-\vartheta(X)).
\tag{J3}
$$

For any set $I$ of primes in $(\sqrt{2X},X)$, define

$$
A_{X,p}=\log(1+1/p)-\epsilon_X\log p,\qquad
B_{X,p}=\epsilon_X\log p+\log(1-p^{-2}).
$$

Then every original factorization satisfies

$$
J_\kappa(n)\ge
\sum_{p\in I}\min\{A_{X,p},B_{X,p},d_\kappa(p)\}.
\tag{J4}
$$

Indeed, if $v_p(n)=0$, its supporting deficit is $A_{X,p}$.
If $v_p(n)=1$, that deficit vanishes but the local reciprocal loss is
$d_\kappa(p)$. If $v_p(n)=a\ge2$, then

$$
\begin{aligned}
S_{X,p}(a)
&=\log Z(p)-\log Z(p^a)+\epsilon_X(a-1)\log p\\
&\ge\log(1-p^{-2})+\epsilon_X\log p=B_{X,p},
\end{aligned}
$$

because $Z(p^a)/Z(p)\le(1-p^{-2})^{-1}$. Adding its nonnegative
reciprocal loss preserves the bound. Thus deleting or repeating a prime
cannot remove its exponent-one loss without paying another deficit.

Fix $0<a<b<1$. Uniformly on $aX<p<bX$,
$A_{X,p},B_{X,p}\gg_{a,b}X^{-1}$. For example,
$XA_{X,p}=X/p-1+o(1)$ and $XB_{X,p}=1+o(1)$ there.
The local formula (L1) also gives

$$
d_\kappa(p)\ge
\frac{\log(\kappa/(p+1))}{\kappa-1}.
$$

Along any prescribed schedule $\kappa=K(X)$ with $K(X)/X\to\infty$,
the common lower bound
$\log(\kappa/(X+1))/(\kappa-1)$ is positive and $o(X^{-1})$.
All three entries in (J4) therefore exceed that bound eventually.
The prime number theorem on each fixed band, followed by
$a\downarrow0$ and $b\uparrow1$, yields

$$
J_{K(X)}(n)\ge(1-o(1))\frac X L
\frac{\log(K(X)/(X+1))}{K(X)-1}.
\tag{J5}
$$

The error is independent of the actual prime-exponent choices. The
statement holds along $X=\log n\to\infty$ for all integers $n$; no CA
assumption on $n$ has been made. After proving the sign at $K(X)$,
Molnar's existing parameter monotonicity covers every real
$1<\kappa\le K(X)$.

## The signed prime error after the supporting-price cancellation

Write $R(t)=\vartheta(t)-t$ and

$$
T(X)=\sum_{p>X}\left[-\log(1-p^{-1})-\frac1p\right]\ge0.
$$

Reuse the [prime-reciprocal partial-summation identity in the Nicolas
application](../ArithSums/nicolas2025comparison.md), with the Mertens
constant fixed by the existing product asymptotic. It transforms (J3) into

$$
\begin{aligned}
E(X)={}&\left(\frac1{XL}-\epsilon_X\right)R(X)\\
&-\int_X^\infty R(t)
\frac{\log t+1}{t^2(\log t)^2}\,dt-T(X),
\end{aligned}
\tag{J6}
$$

where

$$
0<\frac1{XL}-\epsilon_X\le\frac1{2X^2L}.
\tag{J7}
$$

The prime sum uses $p\le X$, so the complementary tail uses $p>X$,
including at prime endpoints. The price cancels the leading endpoint
term $R(X)/(XL)$; the remaining integral retains its sign. Neither
(J2) nor this cancellation alone supplies positivity.

### Eventual ranges from existing unconditional prime estimates

Let $f(u)=u^{3/5}(\log u)^{-1/5}$. Chiara Bellotti's
[*A new zero-density estimate for $\zeta(s)$ and the error term in the
Prime Number Theorem*, arXiv:2508.02041v1](https://arxiv.org/pdf/2508.02041v1),
printed pp.2--3, Theorem 1.5 and Corollary 1.6, report

$$
|R(t)|\ll t\exp(-d f(\log t)),\qquad
d=\left(\frac{5^6 A_0^3}{2^2 3^4}\right)^{1/5},\quad
A_0=\frac1{48.0718}.
$$

This is a preprint supplier, without an RH assumption. Its displayed
theta statement and constants were inspected; its full analytic proof
has not been independently verified here. It is not a reciprocal Robin
theorem. Using that bound in (J6), and $f'(L)\sim3f(L)/(5L)$, gives

$$
E(X)\ll\int_L^\infty\frac{e^{-df(u)}}u\,du
\ll\frac{e^{-df(L)}}{f(L)}.
$$

The endpoint in (J7) is smaller, and $-T(X)\le0$ can be discarded for
this upper bound. Define

$$
K_{\mathrm B}(n)=
\frac{X e^{df(L)}f(L)^2}{L\log L}.
\tag{J8}
$$

Here $K_{\mathrm B}/X\to\infty$ and
$\log(K_{\mathrm B}/X)=df(L)+O(\log L)$. Equation (J5) gives

$$
J_{K_{\mathrm B}(n)}(n)
\ge(d-o(1))\frac{\log L}{f(L)}e^{-df(L)}.
$$

The extra $\log L$ pays the unspecified constant in the prime-error
bound. Thus the paper application of this supplier is

$$
\exists n_0\ \forall n\ge n_0\ \forall\,1<\kappa\le K_{\mathrm B}(n):
\qquad Q_\kappa(n)<B(n).
\tag{J9}
$$

The integers $n$ are unrestricted; $\kappa$ is real. No numerical
$n_0$ is supplied. This range is $X^{1+o(1)}$, so it includes
$C X(\log X)^A$ eventually for every fixed $A\ge0,C>0$ but remains
below the $X^{3/2}$ diagonal. These quantifiers do not supply a cutoff
uniform in $A,C$.

A separate, earlier supplier is
[Johnston--Yang v2](../Weil/johnstonyang2022pnt.md), Theorem 1.4,
equation (1.8), printed p.2:

$$
|R(t)|\le0.027t(\log t)^{1.801}e^{-0.1853 f(\log t)}
\quad(t\ge23).
$$

The same calculation gives the explicit parameter formula

$$
K_{\mathrm{JY}}(n)=
\frac12\frac{X e^{0.1853 f(L)}}{L^{1.601}(\log L)^{2/5}}.
\tag{J10}
$$

For clarity about the constants, put $c=0.1853$ and
$W(L)=L^{1.201}(\log L)^{1/5}e^{-cf(L)}$. The upper bound obtained
from (J6) is
$E(X)\le(0.027/((3/5)c)+o(1))W(L)$, whereas (J5) gives
$J_{K_{\mathrm{JY}}(n)}(n)\ge(2c-o(1))W(L)$.
Since $2c=0.3706>0.027/((3/5)c)$, the counterpart of (J9) holds
with $K_{\mathrm{JY}}$ using this supplier alone. A specified parameter
formula does not specify the first valid integer cutoff.

### A fixed zero-free half-plane as a separate input

Suppose $1/2<\beta<1$ and $\zeta(s)\ne0$ for $\Re s>\beta$.
The integrated explicit formula supplies

$$
\int_2^t(\Psi(u)-u)\,du
=-\sum_\rho\frac{t^{\rho+1}}{\rho(\rho+1)}+O(t).
\tag{J11}
$$

For a primary locator, see Adrian Dudek,
[*On the Riemann Hypothesis and the Difference Between Primes*,
arXiv:1402.6417v2](https://arxiv.org/pdf/1402.6417v2),
section 2.1, equations (3)--(4), printed pp.3--4. The formula follows
by integrating (3); the zero sum is absolutely convergent, with every
zero counted with multiplicity. Its lower-end constants and linear
term fit in $O(t)$ without RH. The numerical $12/5$ remainder in
Dudek's Lemma 4 uses RH and is not used here.

Under the stated half-plane input the zero sum is $O_\beta(t^{\beta+1})$.
The prime-power difference $\Psi-\vartheta$ contributes
$O(t^{3/2}(\log t)^2)$ after integration, which is smaller because
$\beta>1/2$. Consequently

$$
\int_2^t R(u)\,du=O_\beta(t^{\beta+1}).
$$

Integrating (J6)'s tail once more by parts gives
$E(X)\le O_\beta(X^{\beta-1}/L)$. For its separate endpoint term,
the unconditional $R(X)=O(X)$ together with (J7) already suffices;
no pointwise error has been inferred from an integrated estimate.
Taking

$$
K_\beta(n)=X^{2-\beta}\frac L{\log L}
\tag{J12}
$$

in (J5) gives
$J_{K_\beta(n)}(n)\ge(1-\beta-o(1))
X^{\beta-1}(\log L)/L$. Thus, under this half-plane assumption,
there is an $n_0(\beta)$ beyond which every integer $n$ and every real
$1<\kappa\le K_\beta(n)$ satisfy the normalized inequality.

The [Liu v2 source card](../Analytic/liu2026quasirh.md),
Theorem 27.1, reports such a half-plane with
$\beta_0=0.874957019420098946\ldots$. Its substitution into (J12)
gives exponent $2-\beta_0=1.125042980579901054\ldots$.
The already recorded [Sang v1 source](../Zeros/sang2026seveneighths.md),
[Theorem 1.1, section 1.2](https://arxiv.org/html/2610.15291v1#S1.SS2),
states the stronger boundary
$\beta_{\rm S}=8748867/10000000$ for every Dirichlet $L$-function,
including $\zeta$, under its section 2 analytic inputs, explicitly
including the family-wide $7/8$ conclusion. Thus those inputs, together
with Sang's stated theorem, give the eventual range (J12) with exponent
$2-\beta_{\rm S}=11251133/10000000=1.1251133$.
Only the resulting zero-free half-plane enters (J11)--(J12); this
application neither reconstructs the cubic-theta argument nor
transports its packet estimates to new lengths. The primary theorem,
its hypotheses and closing argument were inspected. Its imported
analytic proofs, new estimates and external formalizations have not
been independently verified here. These are conditional applications
of known suppliers, with no new zero-free theorem or numerical
starting cutoff; neither exponent reaches the $3/2$ diagonal.

### An unconditional growing range with a numerical starting point

The eventual range (J9) already includes $K(X)=XL^2\log L$.
The additional conclusion here is a numerical starting point and a
uniform margin, obtained by applying existing explicit prime estimates
to (J4), (J6) and (J7). Set

$$
X_0=158822621,\qquad X=\log n\ge X_0,\qquad L=\log X,
\qquad K=XL^2\log L.
\tag{E1}
$$

In particular $X\ge256$ and $L\ge16$: $e<3$ gives
$e^{16}<3^{16}=43046721<X_0$. For
$I=\{p\text{ prime}:X/4<p\le X/2\}$, which lies inside
$(\sqrt{2X},X)$, the
[Rosser--Schoenfeld dyadic count](../Arith/rosser1962approximate.md#dyadic-prime-count-lower-bound),
Corollary 3, equation (3.8), printed p.69, gives

$$
\#I>\frac{3X}{20\log(X/4)}>\frac{3X}{20L}.
$$

For every $p\in I$, the two supporting deficits in (J4) satisfy

$$
\begin{aligned}
A_{X,p}
&\ge\log\frac{X+2}{X+1}>\frac1{2X},\\
B_{X,p}
&\ge\frac1{2(X+1)}-\frac{32}{X^2}\ge\frac1{4X}.
\end{aligned}
$$

For the second line use $\log p\ge L/2$,
$\log(1+1/X)\ge1/(X+1)$ and
$\log(1-p^{-2})\ge-2p^{-2}$. The displayed last inequality
holds for $X\ge256$.
Now put

$$
c=\frac{\log(K/(X+1))}{K-1}.
$$

For $L\ge16$, elementary logarithm bounds give
$\log K=L+2\log L+\log\log L\le2L$,
$K-1\ge XL^2$, and $X\log L/(X+1)>1$. Hence

$$
\frac{2}{XL^2}<c\le\frac{2}{XL}\le\frac1{4X}.
$$

The lower bound follows from
$\log(K/(X+1))>2\log L$ and $K-1<K$.
The local loss bound preceding (J5) gives $d_K(p)\ge c$.
Thus all three entries of (J4) are at least $c$, independently
of the original integer's exponent choice, and

$$
J_K(n)>\frac{3}{10L^3}.
\tag{E2}
$$

For the upper bound use
[Dusart, arXiv:1002.0442v1](https://arxiv.org/pdf/1002.0442v1),
Theorem 5.2, printed p.4, the row
$k=3$, $\eta_k=0.78$, $x_k=158822621$. Its unconditional statement is

$$
|R(t)|<\frac{39t}{50(\log t)^3}\qquad(t\ge X_0).
$$

This row applies throughout (J6)'s tail. Discarding $-T(X)\le0$
and using (J7), with the full integral retained, gives

$$
\begin{aligned}
E(X)
&\le\frac{39}{100XL^4}
 +\frac{39}{50}\int_X^\infty
   \frac{\log t+1}{t(\log t)^5}\,dt\\
&=\frac{39}{100XL^4}+\frac{13}{50L^3}
  +\frac{39}{200L^4}<\frac7{25L^3}.
\end{aligned}
\tag{E3}
$$

Indeed, multiplying by $L^3$, the upper bound is at most
$13/50+39/(200\cdot16)+39/(100\cdot256\cdot16)<7/25$.
Together with (J2)--(J3) and (E2), this proves the paper application

$$
\boxed{
\log\frac{Q_\kappa(n)}{B(n)}<-\frac1{50L^3}
\quad\left(\log n\ge158822621,\quad
1<\kappa\le(\log n)(\log\log n)^2\log\log\log n\right).
}
\tag{E4}
$$

The quantifiers include every integer $n$ in this domain and every real
parameter in the interval; Molnar's parameter monotonicity transfers
the bound at $K$ to all smaller $\kappa>1$. The only additional quantitative analytic inputs
are the cited dyadic count and Dusart's theta row. Their analytic proofs
and numerical tables have not been independently recertified, and
this application has not been Lean compiled. It makes no originality
claim. The asymptotically larger range (J9) still has no numerical
starting point, whereas (E4) supplies one for this smaller schedule.
Since $K/X^{3/2}\to0$, (E4) does not reach the RH-equivalent diagonal
or settle classical Robin.

## The remaining signed inequality at the RH scale

For $K(n)=\lceil X^{3/2}\rceil$, (J5) gives

$$
J_{K(n)}(n)\ge(1/2-o(1))X^{-1/2}.
\tag{J13}
$$

One sufficient missing estimate is therefore a fixed $\delta>0$ with

$$
E(X)\le(1/2-\delta)X^{-1/2}\quad\text{eventually}.
\tag{J14}
$$

Alternatively one can retain the information discarded in (J3)--(J5)
and seek $H_X<J_{K(n)}(n)$ directly for $X=\log n$.
Equation (J14) is a sufficient condition, not a necessary one.
The unconditional estimates used above, and the reported
$\beta_0$ half-plane, supply upper bounds too coarse to establish it.
That does not assert that the actual signed error exceeds this scale.
The joint estimates are combined paper applications of the cited
suppliers, without an originality or Lean-verification claim; the
diagonal sign and RH remain unresolved.

## The supporting slack at an actual self-tangent source

The extra term $S_X(n)$ in (J1) cannot be assumed to provide another
main-order allowance on the selected source class. Suppose the same
actual classical CA integer $n$ maximizes $Z(m)m^{-\epsilon_0}$ at

$$
X=\log n>2,\qquad L=\log X,\qquad \epsilon_0=\frac1{XL}.
$$

This is the self-tangent price condition, stronger than merely being
classical CA. The [existing prime-local bridge and source
selection](../Analytic/mantovanelli2026primeworkload.md#the-existing-prime-local-bridge)
supply it for the selected counterexample source. The
[separate proper-GA1 power-excess family application](../Arith/caveney2012sacaga.md#the-same-power-excess-family-also-supplies-proper-ga1-sources)
also supplies it on an unbounded family under RH failure, conditional
on the cited source chain. Those selection arguments are reused;
no unconditional unbounded self-tangent family is asserted here.

Write $S_X(n)=\sum_p S_{X,p}(v_p(n))$. Since $n$ maximizes at
$\epsilon_0$ and $N_X$ maximizes at the smaller price $\epsilon_X$,
their two comparisons give

$$
0\le S_X(n)
\le(\epsilon_0-\epsilon_X)(\log N_X-X),\qquad
\log N_X\ge X.
\tag{T1}
$$

This compares rewards at two prices while keeping the loss on the
original $n$. CNS Lemma 3 gives $\log N_X=O(X)$, so (J7) already
implies $S_X(n)=O(1/(XL))$. There is also a finite bound from the same
source's equations (11), (14)--(15) and Lemma 1. Define

$$
K_X=\left\lceil1+\frac{2L}{\log2}\right\rceil,\qquad
U_{\rm cl}(X)=\vartheta(X)+\vartheta(\sqrt{2X})
+K_X\vartheta((3X)^{1/3}).
$$

The classical layers give $\log N_X\le U_{\rm cl}(X)$ by overcounting
all layers from the third onward. Hence, with $[t]_+=\max\{t,0\}$,

$$
0\le S_X(n)\le\frac{[U_{\rm cl}(X)-X]_+}{2X^2L}.
\tag{T2}
$$

This finite bound uses classical CA thresholds, rather than transporting
the normalized endpoint bound (U4) to a different extremizer.

The leading reciprocal loss itself can also be evaluated using the
already supplied classical structure. Fix $1<a<2$ and take
$\kappa=\lceil X^a\rceil$. Along classical CA integers tending to
infinity, CNS Lemma 3 and the next-prime comparison give
$P^+(n)\sim X$. The exponent-one count $M(n)$ above is therefore
$(1+o(1))X/L$, and only $O(\sqrt X)$ primes have higher exponents.
For an exponent-one factor, (L1) is exactly

$$
(\kappa-1)d_\kappa(p)
=\log\kappa-\log(p+1)
-\log\left(1-\left(\frac p{p+1}\right)^\kappa\right).
$$

The last term is uniformly negligible in their sum, since
$(p/(p+1))^\kappa\le e^{-\kappa/(P^+(n)+1)}$.
Removing the $O(\sqrt X)$ higher-exponent primes from the support
changes its logarithmic prime sum by only $o(X)$. The prime number
theorem consequently gives

$$
\begin{aligned}
(\kappa-1)D_\kappa^{(1)}(n)
&=M(n)\log\kappa
 -\sum_{v_p(n)=1}\log(p+1)+o(X)\\
&=(a-1+o(1))X.
\end{aligned}
$$

Here $D^{(1)}$ denotes just the actual exponent-one terms of $D$.
For its remaining terms, (L3)'s local bound gives
$0\le D_\kappa^{(\ge2)}(n)=O_a(LX^{1/2-a})=o(X^{1-a})$.
Thus classical CA alone supplies

$$
D_{\lceil X^a\rceil}(n)\sim(a-1)X^{1-a}.
\tag{T3}
$$

On the self-tangent subclass, (T1) additionally gives
$S_X(n)/X^{1-a}=O(X^{a-2}/L)\to0$. Therefore

$$
J_{\lceil X^a\rceil}(n)\sim(a-1)X^{1-a},\qquad
J_{\lceil X^{3/2}\rceil}(n)\sim\frac1{2\sqrt X}.
\tag{T4}
$$

These joint-deficit asymptotics retain the self-tangent hypothesis on every source
and do not assert that all integers or all CA numbers have negligible
$S_X$. They show that the coefficient in (J13) is attained at leading
order on any such unbounded family. Increasing the allowance solely
by claiming a larger supporting slack at those same sources cannot
pay the missing signed estimate. Further progress requires control of
$H_X$ there, or another joint constraint not discarded in (J3)--(J5).
This is a paper-level application of the existing source structure and
local formula, without a priority claim, a new RH criterion, or Lean
verification. It does not determine the sign of $H_X-J_\kappa(n)$.

## Consequences for the FIB and same-source Robin routes

The parameter $k$ in the LCM expansion counts divisor entries; the
depth of a `[null,2,3,2 5,5]` address counts successive Zeckendorf
windows. They are different parameters. The source supplies no theorem
identifying either parameter with the other or with a Fourier cutoff.
On a FIB address, (D1) is evaluated at the actual decoded integer.
The occupancy and seam rules alone supply neither the prime-power
factors in (L1) nor the sign required in (D3).
For the joint route (J1)--(J5), a FIB address must retain or recover
the same decoded integer's actual $v_p(n)$ and $X=\log n$, including
whether each prime in the relevant band is absent, occurs once, or is
repeated. Address depth and interval-length conservation do not supply
these arithmetic deficits.
Its normalized extremizers in section 4 likewise optimize a different
function from the classical strict CA stock. Appendix A, printed
pp.21--22, gives an explicit obstruction to using unnormalized
reciprocal endpoints for the normalized Robin test.

Reuse the source's LCM expansion, fixed-parameter expansions, criterion
and certified bounded range before seeking a new estimate. The
[existing unrestricted same-integer identity, OCQ13](../ArithSums/nicolas2025comparison.md#the-original-fixed-exponent-consumer-and-its-remaining-signed-input),
combined directly with (L2), already supplies the interface from this
normalization to the complete $I_\psi(\log n)$, retaining the same
integer's reserve, own-price defect and $D_\kappa(n)$. No new identity
or criterion is needed for that connection. For the
[selected-source route](../Analytic/polak2026finiterobinca.md), the
signed integral's lower bound remains unpaid; for the increment-moment
route, the growing-$s$ error remains unpaid. The
[remote Weil completion, WT11--WT14](../Estimation/trureturing2026pricegapconvexity.md#a-remote-completion-cancels-the-actual-poles-at-small-signed-cost)
pays a correction to its original occupation test, not the missing
signed bound or its transfer to a specified integer. This preprint
supplies neither missing estimate, and its bounded result cannot be
presented as a proof of classical Robin or RH.
