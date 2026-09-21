---
slug: glasby-paseman-powered-ratio-maximum
bibkey: byun2026unimodality
doi: null
url: https://arxiv.org/abs/2604.14639v1
triage: theorem
motivation_gids:
  - D5/S3/TotalVariation/Pinsker.binary_pinsker
---

# Generalized Glasby–Paseman Conjecture 1.1(d)

## Problem

The version-1 source, D5/L/Analytic/byun2026unimodality, page 2, defines
the sequence (1.4) by

\[
R_{m,l,a}(r)=
\frac{\sum_{i=0}^{r}(\binom mi a^i)^l}
     {\sum_{i=0}^{r}(\binom ri a^i)^l},\qquad 0\le r\le m.
\]

Conjecture 1.1(d) asks, for every fixed positive real a and positive
integer l, whether

\[
\lim_{m\to\infty}\frac{\max_{r\in\{0,\ldots,m\}}R_{m,l,a}(r)}{A_m}=1,
\qquad
A_m=\frac{\sqrt l}{\sqrt{2\pi m}}
\frac{\sqrt{1+2a}(1+a)a^{(l-2)/2}}{(1+a)^l-1}
\left(\frac{1+2a}{1+a}\right)^{(m+1/2)l}.
\]

The displayed constant transcribes clause (d); source footnote 1 specifies
the ratio-to-one meaning. Both weighted products are raised to l before
summation. The denominator is a complete row-r powered sum, not
(1+a)^(rl). All integer r with 0<=r<=m are included, and ties are allowed.
The exponent (l-2)/2 uses real subtraction and equals -1/2 at l=1.
The quantifiers fix a and l before taking m to infinity; uniformity in
varying a or l is not asserted.

## Motivation

The question is registered in
https://github.com/the-omega-institute/trureturing/issues/9357 and the
candidate implementation is associated with
https://github.com/the-omega-institute/trureturing/pull/9399.
The frozen Bernoulli Pinsker inequality
D5/S3/TotalVariation/Pinsker.binary_pinsker supplies exponential control
away from a central slope. It does not by itself identify the maximum's
Gaussian prefactor. It is the frozen motivation reference; the seven
binomial modules are not used as already-frozen premises of this dossier.

## Gap

The complete weighted denominator asymptotic is classical:
D5/L/Analytic/abel2013binomial, Theorem 3.1, gives it for l>=2,
and l=1 is exact. D5/L/Analytic/ouimet2020precise supplies local Gaussian
estimates and the l=2,3 normalizations. These inputs do not alone evaluate
the maximum of the truncated ratio.

The remaining analytic distinction is between a fixed comparison index,
the location of every actual maximizer, and a sharp upper estimate along
those maximizers. A limit r(m)/m=a/(1+2a) alone does not control the
Gaussian penalty at the scale needed for the exact prefactor. A floor
comparison provides a lower limit and a uniform sharp binomial bound
provides the matching upper limit, while the powered denominator and
geometric endpoint factor must be evaluated along the same sequences.

The source credits earlier maximum results for l=a=1 and l=1 with positive
integer a, and proves l=2,a=1 itself. They are not new resolved cases in
this dossier. The sole candidate resolution is the full clause (d).

## Route

The formal endpoint is
D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic.
Its definition maximumValue takes the finite maximum over the image of
range(m+1) under poweredRatio, so it includes every allowed index and
does not choose a unique peak. The row-zero extension of the definition
does not affect the source's positive-m asymptotic.

The existing module chain has the following mathematical roles:

| Module under D5/S3/AnalyticClosure | Role and boundary |
| --- | --- |
| BinomialLocalGaussian | Relative Gaussian estimate on the n^(7/12) window, negligible powered tails, and Gaussian lattice sums. |
| BinomialPowerNormalization | Classical complete power-sum normalization for every positive natural l and 0<p<1. |
| BinomialMovingEndpoint | Geometric factor along every sequence with slope 0<q<a/(1+a). |
| BinomialMaximumLocalization | Floor comparison and exponential separation for prefixValue, whose denominator is only (1+a)^(rl). |
| BinomialUniformMaximum | Uniform sharp upper bound for every binomial index, with no mode assumption. |
| BinomialPoweredRatioLocalization | Slope a/(1+2a) for every maximizing sequence of the actual powered-sum ratio. |
| BinomialPoweredRatioMaximum | Floor lower comparison and uniform upper comparison for the actual finite maximum, with the exact published A_m. |

The denominator normalization is applied with p=a/(1+a); the Gaussian
comparison uses q=a/(1+2a). The moving-endpoint factor at q is
1/(1-(1+a)^(-l)). The full powered denominator is retained when combining
these constants. No exact peak, uniqueness, unimodality, log-concavity,
or other part of clauses (a)–(c) is asserted or assumed by the endpoint.

## Falsifier

A fixed a>0, positive integer l, epsilon>0 and an unbounded sequence of
m for which the displayed maximum/A_m stays at least epsilon from one
would refute clause (d). Finite exceptions or disagreement about a unique
peak do not refute this asymptotic. A source-faithful counterexample to
the normalization or either bound in the same parameter range defeats
the proposed analytic route. An already-published exact settlement in
uninspected literature would change open-problem eligibility, not the
truth of the asymptotic.

## Evidence

The exact source statement is on page 2, equation (1.4), Conjecture 1.1(d)
and footnote 1 of the versioned preprint. The bounded source findings in
#9357 include the source body, the local-limit source, all 18 pages of
the weighted binomial-polynomial source (including Theorem 3.1 and proof),
and all 10 pages of D5/L/Analytic/luca2012some. The latter's Lemma 3.1,
pages 6–7, restates an unweighted complete binomial-product theorem;
it is not cited as an arbitrary-weight maximum result.

The seven Lean sources are the mathematical candidate; their authored
Scribe mirrors state the respective claims and supplier boundaries.
This dossier carries no typed Proved claim. Canonical admission and
Freeze, independent mathematical review, required CI, ordinary merge and
an independent completion audit are outside the evidence asserted here.
Neither the support modules nor this metadata preparation confer
completed-delivery or KPI credit.

## Triage

First-tier external named conjecture published in 2026, fixed by #9357.
The endpoint's proposed admission basis is open-problem-resolution for
the complete clause (d). Per-declaration admission and source-fidelity
assessments remain obligations of the independent mathematical review;
this metadata dossier does not grant them. The classical denominator
and local-limit ingredients are literature suppliers, not new discoveries
or additional open-problem resolutions. The target concerns an unbounded
analytic limit, not a finite-instance or support-only completion count.

## ASSUMED-UNVERIFIED

The bounded audit excludes an exact prior settlement only within its
inspected scope. The original Binomial mean body,
DOI 10.1080/02331888.2026.2631025, and McIntosh 1996 body,
DOI 10.1006/jnth.1996.0072, were not read in that audit. Worldwide priority
and the absence of settlements outside that scope are unverified.

The exact-peak and shape conjectures (a)–(c), uniformity in changing
parameters, and a count of multiple new resolved special cases are
excluded interpretations. A simplified prefix denominator, natural
subtraction in the l=1 exponent, or localization alone would not establish
the registered endpoint. Independent acceptance and canonical Freeze of
these seven modules are not asserted by this dossier.
