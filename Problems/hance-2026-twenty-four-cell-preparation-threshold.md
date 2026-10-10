---
slug: hance-2026-twenty-four-cell-preparation-threshold
bibkey: hance2026fourquestions
doi: null
url: https://arxiv.org/abs/2609.10078v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumContext/HanceTwentyFourCellThreshold.result
---

# Exact preparation-noncontextuality threshold of the twenty-four-cell

## Problem

Jonte R. Hance, *Why three? A two-level system with four mutually unbiased
questions*, arXiv:2609.10078v1, “Polytopes, quasiprobabilities and contextuality”,
after Eq. (sbound), source main.tex line 182:

> The 24-cell subtheory is therefore preparation contextual at least for $\lambda>2/3$; whether its further equivalences lower the threshold, and whether it is measurement contextual, we leave open, and both are linear programs.

Only the further-preparation-equivalences threshold clause is addressed.
Let $V=\{\pm e_i:1\leq i\leq4\}\cup\{s/2:s\in\{\pm1\}^4\}$.
Take one direction from each of its twelve antipodal pairs as a sharp binary
question, with both outcomes. For every real $\lambda\in[0,1]$ the statistics are
$p(b\mid n,x)=(1+b\lambda n\cdot x)/2$. All classical convex mixtures are included.

A model has an arbitrary measurable ontic space, countably additive probability
preparations and arbitrary measurable nonnegative normalized binary responses.
Every pair of operationally equal convex preparation mixtures has equal ontic
mixture measures. There is no measurement-noncontextuality or determinism premise.

## Motivation

`D5/S3/QuantumContext/HanceTwentyFourCellThreshold.result` states, in every
universe, that such a model exists if and only if $\lambda\leq1/2$.
It includes all twenty-four preparations, all twelve sharp questions, all
mixture equivalences and the zero-visibility collapse.

## Gap

The source's regular-hexagon obstruction excludes visibility above $2/3$.
The parity-oblivious random-access-code bound, attributed to Spekkens et al.
in Chailloux et al., arXiv:1404.5153v3, already supplies the stronger upper
obstruction $1/2$. Full-scenario attainment is the additional requirement.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/14971.
The scoped source and literature searches recorded there found no exact full
scenario settlement; those searches do not certify exhaustive absence.

## Route

For each of the sixteen sign tuples $s$, the mixture assigning weight $1/6$
to each signed axis $s_i e_i$ and weight $1/3$ to $-s/2$ has zero Bloch vector.
Its ontic measure equals the coordinate midpoint measure. Products of the four
stochastic coordinate responses define nonnegative measurable sign weights,
whose sum is one and whose marginals are the coordinate responses.
Integrating the mixture identities against these weights and summing gives
$4(1+\lambda)\leq6$. This argument applies directly to the original measures.

For the converse use all $24$ vectors
$U=\{\epsilon e_i+\delta e_j:i<j,\epsilon,\delta\in\{\pm1\}\}$, with

$$
\mu_x(u)=\frac{1+2\lambda u\cdot x}{24},\qquad
\xi(b\mid n,u)=\frac{1+b u\cdot n}{2}.
$$

The dot products lie in $[-1,1]$, $\sum_u u=0$, and
$\sum_u uu^T=12I$. These give probability preparations, stochastic responses
and exact statistics. The preparation mass is affine in the actual noisy
mixture vector, so every operational equivalence is preserved without division
by visibility.

## Falsifier

The iff preregistered in issue #14971 would be refuted by a model satisfying
the stated full scenario at any $\lambda>1/2$, or by nonexistence at any
$\lambda\in[0,1/2]$. Omitting preparations, questions, convex equivalences or
the zero-visibility collapse, or restricting the upper argument to finite
ontic spaces or deterministic responses, would not settle that statement.

## Evidence

The source locators and model conventions are in
`Library/QuantumContext/hance2026fourquestions.md`; the known upper obstruction
and its attribution are in `Library/QuantumContext/chailloux2016parityoblivious.md`.
Issue #14971 records the full-scenario statement before the Lean probe.
`D5/S3/QuantumContext/HanceTwentyFourCellThreshold.lean` proves `result` for every
universe and every $\lambda\in[0,1]$, with the iff stated in Motivation and the
arbitrary-space obstruction and full affine attainment described in Route.

## Triage

### What the settlement shows

Proved by the result GID above: the exact threshold is $1/2$, including equality.
The decisive attainment is the twenty-four-state model for every visibility
from zero to one half. At zero it is uniform for every preparation; all collapsed
operational equivalences are respected. The upper argument uses arbitrary
measurable spaces and stochastic responses, and introduces no RN or finite-space
representation premise.

The source's hexagon bound and its noiseless preparation-contextuality conclusion
remain compatible with this sharper full-scenario result. The separate question
of measurement contextuality remains open. Extensions to other preparation
polytopes or measurement sets are open and are not asserted by this theorem.

## ASSUMED-UNVERIFIED

The scoped literature searches do not establish worldwide novelty or priority;
the known upper obstruction is not claimed as new. The Reg audit remains
`declared_unresolved` (`IE-C050 / unclassified_form / source.observation_data`)
under issue #14971, with no validated certificate. Measurement contextuality
and extensions beyond this preparation and question scenario remain open.
