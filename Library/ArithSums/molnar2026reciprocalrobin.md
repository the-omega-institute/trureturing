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
belong to Molnar; this note adds no originality or peer-review claim.

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
[Fan--Kobayashi--Molnar note](fankobayashimolnar2025family.md).
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

## Consequences for the FIB and same-source Robin routes

The parameter $k$ in the LCM expansion counts divisor entries; the
depth of a `[null,2,3,2 5,5]` address counts successive Zeckendorf
windows. They are different parameters. The source supplies no theorem
identifying either parameter with the other or with a Fourier cutoff.
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
