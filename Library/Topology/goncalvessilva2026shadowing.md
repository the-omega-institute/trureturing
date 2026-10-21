---
bibkey: goncalvessilva2026shadowing
authors: Daniel Goncalves and Sofia Meneghel Silva
year: 2026
title: 'Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets'
doi: null
url: https://arxiv.org/abs/2603.03200v1
claim: The Section 3 open question asks whether uniform equivalence preserves Lipschitz shadowing for compatible product metrics on a countably infinite alphabet.
strata_touched: []
license: citation-only
triage: anchor
---

# Uniform metric changes on the countably infinite product shift

The literal open question on printed/PDF p.6 quantifies over arbitrary metrics
uniformly equivalent to the standard product metric on a product subshift of
a countably infinite discrete alphabet. It is not restricted to the globally
symbol-independent prefix metrics of Definition 3.3.

Definitions 2.2 and 2.3 use strict pseudo-orbit and tracing inequalities. Tracing
includes time zero and every subsequent natural time. Lipschitz shadowing
chooses positive L and a positive cutoff before every control parameter in
the positive interval ending at that cutoff and every infinite pseudo-orbit.
Definition 2.4 requires both identity maps to be uniformly continuous.

The head-dependent metric and its counterexample are developed in
`D5/S1/Dynamics/Shadowing/ProductMetricCounterexample`. They are new deductions
addressing the source question, not results attributed to the paper. The
constructor and infinite diagonal-splice suppliers are in `HeadWeightedMetric`
and `MetricTracing` in the same directory. Mathlib's `PiNat` supplies the first
difference, cylinders and the actual standard product metric; the existing
`UniformTracing` module supplies the noncompact uniform shadowing contract.

Definition 2.1's preliminary Deaconu--Renault terminology assumes local
compactness. The full product of a countably infinite discrete alphabet lacks
that property. The formal target is the unrestricted literal Section 3
question, and makes no local compactness claim. A locally compact variant is
outside these declarations.

The checked source is v1. The bounded later-literature search has not located
a later answer; it does not certify global uniqueness or publication priority.

## Verified locator

Versioned primary source: https://arxiv.org/abs/2603.03200v1.
PDF: https://arxiv.org/pdf/2603.03200v1.

Definitions 2.1--2.4 are on printed/PDF p.3. Definition 3.3 is on p.5;
Corollary 3.5, Remark 3.6 and the literal product-metric open question are on
printed/PDF p.6. The supplied primary PDF has SHA-256
`9e30b597eee45fb3cb1fb1e1612a9042c13ef13ef2fa6f6b23bf08d933c01494`.

## Quantitative boundary supplied by the repository

`HeadWeightedLipschitz` gives the exact equivalence between Lipschitz shadowing
for the raw head-weight metric and a single C>0 satisfying
`weight(s,n) <= C * weight(t,n-1)` for all heads s,t and n>=1. The weights are
positive, nonincreasing in depth and normalized to one at depth zero. No
uniform lower bound, common vanishing upper envelope, continuity assumption
or product uniformity is added to the raw tracing predicate.

Sufficiency uses the infinite diagonal-mismatch telescope. For necessity,
proposed positive controls L,c give C=max(2L,max(2/c,1)). A violating ratio
has C*weight(t,n-1)<1, so its doubled edge error is already below c. The
existing single-defect infinite pseudo-orbit then excludes every full tracer
at the proposed Lipschitz radius. This replaces the earlier finite-depth
cutoff argument and removes its UniformBounds hypothesis.

When UniformBounds are available, the product-uniform metric has exactly
the same distance, so the theorem supplies the original product-compatible
classification as an exact application. The constant weight family is also
covered: it gives the discrete metric and has no uniformly vanishing upper
envelope. This is repository-derived, not attributed to the source and not
another count of the already proved unrestricted metric counterexample.
The separately scoped locally compact problem and arbitrary compatible-metric
classification remain outside this statement.

The unversioned primary arXiv page was read back on 2026-10-21: submission
history still lists only v1 (3 March 2026), and its abstract still describes
arbitrary uniform-metric product-model stability as unclear. This primary
version check does not certify that no other publication has answered it.
