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

For every fixed $0<c<h$, choose, for sufficiently large integers $n$,

$$
j_c(n)=\left\lceil
\frac{c\log n}{\log\log n\,\log\log\log n}
\right\rceil.
\tag{U3}
$$

Then $\log N_{j_c(n)}^{\mathrm{eff}}/\log n\to c/h<1$.
The source's uniform bounded-interval conclusion therefore supplies

$$
Q_\kappa(n)<B(n)
\quad\text{for every }n\ge n_0(c)
\text{ and every real }1<\kappa\le j_c(n).
\tag{U4}
$$

No numerical value of $n_0(c)$ is obtained here. The case $c=h$ is
unsettled by this asymptotic. For $c>h$, this particular cutoff no longer
certifies $n\ge N_{j_c(n)}^{\mathrm{eff}}$; that does not refute the
inequality. This is an application of the explicit source cutoff, not
an exchange of the quantifiers in a fixed-parameter eventual theorem,
and not a new estimate for classical $Z(n)$.

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
Nor does (U4): at $k(n)\sim(\log n)^{3/2}$, (U2) gives
$\log N_{k(n)}^{\mathrm{eff}}/\log n\to\infty$.
This explicit cutoff is insufficient for (D3), even though it already
certifies a slower growing schedule.
The loss, CA-visibility and diagonal arguments above were not located in the
inspected Molnar v1 statement; they are
recorded here as combined applications of existing inputs, without a
priority or Lean-verification claim.

## Consequences for the FIB and same-source Robin routes

The parameter $k$ in the LCM expansion counts divisor entries; the
depth of a `[null,2,3,2 5,5]` address counts successive Zeckendorf
windows. They are different parameters. The source supplies no theorem
identifying either parameter with the other or with a Fourier cutoff.
On a FIB address, (D1) is evaluated at the actual decoded integer.
The occupancy and seam rules alone supply neither the prime-power
factors in (L1) nor the sign required in (D3).
Its normalized extremizers in section 4 likewise optimize a different
function from the classical strict CA stock. Appendix A, printed
pp.21--22, gives an explicit obstruction to using unnormalized
reciprocal endpoints for the normalized Robin test.

Reuse the source's LCM expansion, fixed-parameter expansions, criterion
and certified bounded range before seeking a new estimate. For the
[selected-source route](../Analytic/polak2026finiterobinca.md), the
signed $I_\psi(A)$ lower bound remains unpaid; for the increment-moment
route, the growing-$s$ error remains unpaid. This preprint supplies
neither missing estimate, and its bounded result cannot be presented
as a proof of classical Robin or RH.
