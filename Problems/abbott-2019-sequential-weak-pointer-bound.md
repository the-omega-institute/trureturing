---
slug: abbott-2019-sequential-weak-pointer-bound
bibkey: abbott2019anomalous
doi: 10.22331/q-2019-10-14-194
url: https://arxiv.org/abs/1805.09364v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result
---

# Three weak measurements of projections below minus one eighth

## Problem

A. A. Abbott, R. Silva, J. Wechs, N. Brunner and C. Branciard (arXiv:1805.09364,
quant-ph; Quantum 3, 194 (2019)) study sequential weak measurements without
post-selection. For `n` observables `A_1, …, A_n` and a state `ρ`, the mean
product of the pointer positions in the weak regime is
`2^{−(n−1)} Tr[{A_1, {A_2, …, {A_{n−1}, A_n}…}} ρ]`. For two projection
observables (eigenvalues 0 and 1) the paper proves that this is at least
`−1/8`, and states:

> Interestingly, by numerically minimising the mean product of the pointer
> positions for sequences of up to 5 projection observables, we were unable to
> obtain a value smaller than −1/8, and we conjecture that this is in fact the
> case for all n.

Issue #11377 fixes the reading. A projection observable is an orthogonal
projection `P = P² = P*` on `ℂ^d` of any rank, as in the paper's two-observable
theorem. The formal `claim` is the conjecture for every dimension, every
number of projections and every unit vector; the result refutes it.

## Motivation

For two projection observables the paper's example attains `−1/8`, and its
Appendix shows that this is "the most anomalous value obtainable"; the
conjecture asserts that longer sequences of projections do not go further.
The frozen declaration
`D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result` shows that
three projections on `ℂ³` already reach `−1/6`.

## Gap

Issue #11377 preregisters the reading, the counterexample and the literature
check. The conjecture sentence is in all three arXiv versions. INSPIRE lists 13
citing records; the 8 with arXiv full texts were read for the bound and for
nested anticommutators, and none treats three or more projection observables.
The two-projection bound `{P, Q} ≥ −1/4` gives only the case `n = 2`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Take `d = 3`, the state `e_3`, the projection `P_1` onto `(1, 1, −1)`, and
   `P_2 = I − v v*`, `P_3 = I − w w*` with `v = (0, 1, −1)/√2`,
   `w = (1, 0, −1)/√2`; all three have rational entries.
2. Check `P² = P = P*` for each and `⟨e_3, e_3⟩ = 1` entrywise.
3. Evaluate `(1/4)⟨e_3, {P_1, {P_2, P_3}} e_3⟩ = −1/6 < −1/8`. The paper's
   three-observable form `½(Re⟨P_3P_2P_1⟩ + Re⟨P_2P_3P_1⟩)` gives the same value.

## Falsifier

The answer would change if "projection observable" were read as a rank-one
projection only: the counterexample uses projections of rank 2, and the
numerical searches with rank-one projections recorded in issue #11377 (all
qubit sequences in particular) reached `−1/8` and no lower for three to seven
observables. The paper
defines projection observables by their eigenvalues 0 and 1 and proves its
two-observable bound for any rank; the dimension of its numerical search is not
stated.

## Evidence

Exact rational arithmetic (issue #11377) reproduces `−1/6`, the paper's qubit
example and its two-observable bound `−1/8` as positive controls.

The canonical source is
`D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.lean`. Its public
declarations are `nestedAnti`, `pointerMean`, `claim` and `result`. The frozen
module state has statement identity
`sha256:8868bbf444c74a1adf9cd33157f6d92fe05a818dec792c771701d3a7dc9d79fa`.
The result declaration has statement identity
`sha256:7d8c1049cbc7f723c163a9ceacd5bfd84f73a4add72eef062d9b4799517033cf`.
The Freeze event is
`sha256:2d7203096b4e87e36b736800c54da6d048df6dd2e82ac1e51d37d721b968de2e`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2019 quant-ph paper, preregistered in issue #11377
before any Lean. `theorem`; resolution `refuted`. The public theorem has
`proof_shape: bind-only`: it evaluates the definitions at the explicit
instance. Its admission basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

## ASSUMED-UNVERIFIED

The published Quantum text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
