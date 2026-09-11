---
bibkey: meiburg2025purecomplement
authors: Alex Meiburg
year: 2025
title: Quantum notions of information and entropy — complementary pure-state marginals
doi: null
url: https://github.com/leanprover-community/physlib/blob/889c09c66fb5f3c4a27182a43cafbed9e00b9d0a/QuantumInfo/Entropy/VonNeumann.lean
claim: The two complementary marginals of a finite pure state have equal von Neumann entropy.
strata_touched:
  - D5/S3/Quantum/Information/InputInformationBalance
license: Apache-2.0
triage: anchor
---

# Complementary entropy of a pure state

## Verified locator

The pinned source is:
https://github.com/leanprover-community/physlib/blob/889c09c66fb5f3c4a27182a43cafbed9e00b9d0a/QuantumInfo/Entropy/VonNeumann.lean
It supplies `Sᵥₙ_of_partial_eq` and `Sᵥₙ_pure_complement`, using equality of the
nonzero characteristic roots of rectangular products. The source was retrieved and read.
The source header identifies Alex Meiburg, copyright 2025, and Apache 2.0.
The complete license is retained in `docs/reports/inoutbalance/physlib-LICENSE.txt`.
The upstream root tree contains no NOTICE file. Its Lean and mathlib versions match
the repository pin; the repository's A17 direct-dependency admission remains open,
so the existing DensityState interface receives a source-attributed port under A17.2.

The companion information identity follows by applying this equality to the AB/R
and AR/B cuts of the same pure state, then expanding the two mutual informations.
The port uses the repository's existing partial traces and trace-based entropy.
The three-body regrouping is explicit, and the single-system marginal equalities
are proved for those constructed states.

Retire the port when this repository's pinned mathlib provides equivalent declarations.
Implementation and verification are by one Codex worker using the lean4 skill;
this note does not claim an independent review.
