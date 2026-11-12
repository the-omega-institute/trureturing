---
slug: mathoverflow-509794-accumulated-sparse-errors
bibkey: ekene2026accumulatedpsd
doi: null
url: https://mathoverflow.net/revisions/509794/2
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/AccumulatedSparseRefutation.result
  - D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result
---

# Accumulated sparse approximation errors

## Problem

Ekene E., [MathOverflow 509794, revision 2](https://mathoverflow.net/revisions/509794/2), poses one source event with two separately required assertions. Attribution and CC BY-SA 4.0 terms are recorded in the [Library note](../Library/QuadraticForms/ekene2026accumulatedpsd.md).

> Let $K$ be a positive semidefinite contraction on $\mathbb R^m$, let $x \in \mathbb R^m$ satisfy $x_i \geq 0$, $\|x\|_2 = 1$, and $K_{ii} \leq x_i^2$. Define
> $$\tau_d(K,x)^2=\min_{\substack{z\in\mathbb R^m\\|\mathrm{supp}(z)|\leq d}}(x-z)^\top K(x-z).$$
> Prove that $\sum_{d=1}^{m-1}\tau_d(K,x)^2\leq1$.

> Let $H$ be a real Hilbert space, let $\mu$ be a probability measure on the unit ball of $H$, and set $v=\int a\,\mathrm d\mu(a)$. Then with
> $$\sigma_d(v)^2=\inf\left\{\left\|v-\sum_{j=1}^dc_ja_j\right\|^2:a_1,\ldots,a_d\in\mathrm{supp}(\mu),\ c_1,\ldots,c_d\in\mathbb R\right\},$$
> we have $\sum_{d=1}^\infty\sigma_d(v)^2\leq1$.

Both universal assertions retain their full domains. A counterexample has dimension 64; that number does not restrict either claim. There is one grouped event, requiring two literal negation theorems, rather than a negation of their conjunction.

## Motivation

The question asks whether sparse errors can accumulate to more than one despite a diagonal domination condition, and whether the analogous best-term Hilbert errors admit the same bound.

## Gap

The finite errors must be actual attained minima over all real coefficients. The Hilbert errors must use the actual measure support and Bochner integral and admit an ordinary sum. These semantic connections cannot be replaced by a formula stipulated as the optimum.

## Route

Use $x_i=1/8$ and $K=(I+J)/128$ on 64 coordinates. A supportwise Cauchy--Schwarz inequality and an explicit attaining vector give $65(64-d)/(8192(d+1))$ for $1\leq d\leq64$. The Hilbert realization uses 64 atoms $(e_0+e_i)/\sqrt2$ in Euclidean 65-space and their uniform probability on the closed unit-ball subtype. Repeated tuple entries are consolidated by fibers; zero coefficients pad smaller supports. The Gram scaling identifies the two actual error sets. The Hilbert errors vanish for every $d\geq64$.

## Falsifier

Failure of positive semidefiniteness, Euclidean contraction, diagonal domination, an all-real lower bound, attainment, the actual support or integral identity, either direction of the tuple correspondence, or the zero-tail ordinary-sum bridge prevents the proposed grouped refutation.

## Evidence

The two members are `D5/S3/QuadraticForms/AccumulatedSparseRefutation.result` and `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result`. Each negates its own closed full-domain claim. The finite proof supplies attained all-real minima; the Hilbert proof supplies the actual atomic support, integrable Bochner barycenter, equality of the source optimizing sets and a zero-tail ordinary sum. Freezing and completed-event status remain separate obligations.

## Triage

Tier 1, preregistered in [#28173](https://github.com/the-omega-institute/trureturing/issues/28173) before the independent paper probe. A bounded official primary-source observation gives zero answers and an unchanged two-clause body. It does not establish worldwide priority or exhaustive openness. The single source event remains incomplete until both original negations and the later verification and delivery obligations hold.

### What the construction tests

The failure mechanism is a shared atom component together with independent coordinates: optimization leaves a harmonic contribution across sparsity levels. The same fixed matrix and atomic geometry realize all the minima in the accumulated sum. Possible additional hypotheses or sharper universal bounds remain open.

## ASSUMED-UNVERIFIED

Canonical scoped reporting, independent source fidelity, rendered projections, formal admission, required checks and publication remain unfinished. The public-helper registration audit is unfinished under the [source-owner issue exception](https://github.com/the-omega-institute/trureturing/issues/28173#issuecomment-6777232269). The dossier makes no completed-event or KPI claim.
