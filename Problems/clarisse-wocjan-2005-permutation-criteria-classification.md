---
slug: clarisse-wocjan-2005-permutation-criteria-classification
bibkey: clarissewocjan2005permutationcriteria
doi: null
url: https://arxiv.org/abs/quant-ph/0504160
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
---

## Problem

Clarisse and Wocjan, *On independent permutation separability criteria*,
arXiv:quant-ph/0504160v2, Definition 1, identify two permutation criteria
when their rearranged matrices have equal trace norm on every positive
trace-one quantum state. Section V states:

> to give a complete characterization of the independent criteria is an open problem.

It also states:

> It is unlikely that there are more dependences in the criteria from Theorem 3.

For every number of parties r at least one, every local dimension d at least
two, and every pair of permutations sigma and mu of the 2r interleaved
positions, the target is the following equivalence. Norm dependence on all
density matrices holds if and only if their row-position sets are related
by identity, complement, simultaneous exchange of the two positions in
every party, or exchange followed by complement.

## Motivation

`FiniteTraceDistance.traceNorm` supplies an existing finite-matrix norm
with kernel-checked spectral and positive-semidefinite properties.
The source's index permutations act directly on operators in that setting.
A complete separation argument gives an exact classification of Definition 1;
the numerical class count is a separate finite orbit calculation.

## Gap

The known four transformations preserve the norm function on states.
Necessity requires concrete positive trace-one states that distinguish
every pair of row sets outside their orbit under the four transformations (at most four elements). Merely counting
those orbits does not establish analytic separation.

## Route

Use zero-based positions 2k and 2k+1 for ket and bra coordinates.
For a permutation sigma, its row set is the set of original positions
sent to even output positions. Equal row sets give independent row and
column reindexings. Complement gives transpose. Exchanging every party's
two positions gives entrywise conjugation on Hermitian inputs.

At each party, the maximally mixed qubit with all other parties fixed to
zero separates equal-side labels from opposite-side labels. A Bell pair
on every two distinct parties separates the three possible distances
between their paired side labels. Equal-side membership and those distances
recover the labels up to two global binary choices, exactly the four
known transformations.

## Falsifier

A pair of row sets outside the four transformations with identical norm
functions on all positive trace-one states would refute the target.
A failure of a proposed witness norm must first be checked against its
actual matrix entries and positive trace-one normalization. A failure of
one witness construction alone does not refute the target classification.

## Evidence

The supplied source excerpts fix the state space, index convention,
trace norm, dependence relation, and proposed upper bound. The supplied
preregistration is issue 30402. Repository implementations are under
`D5/S3/Quantum/Entanglement/PermutationCriteria/`.
`ClarisseWocjanClassification.result` proves the displayed equivalence for
every r at least one and every d at least two. Its complete import closure
has a successful scoped Lean report. The theorem's axiom closure consists
of `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

### What the settlement shows

The proof mechanism is separation by single-party mixed states and
two-party Bell states, followed by recovery of the known four symmetries.
The domain includes every r at least one and every d at least two; the
witnesses occupy only the first two local basis vectors.

The theorem concerns equality of trace-norm functions in Definition 1.
It does not establish the source's stronger “truly independent” property,
which concerns comparison of the sets of states detected by different
criteria. That question remains separate.

The four-symmetry orbit count associated with OEIS A045723, for r at least
one, is

$$\frac{\binom{2r}{r}+2^r+\mathbf{1}_{2\mid r}\binom{r}{r/2}}{4}.$$

The classification characterizes dependence by those orbits. This closed
count is not formalized here; it additionally needs a finite orbit-count
calculation, for example Burnside's lemma.

## ASSUMED-UNVERIFIED

The bibliographic identity and quotations are taken from the supplied
brief. No independent online search for subsequent resolutions is claimed
in this offline environment. No claim of priority over later literature
is made. The optional exact class count remains unproved in this delivery.
