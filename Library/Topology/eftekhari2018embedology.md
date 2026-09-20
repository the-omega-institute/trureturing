---
bibkey: eftekhari2018embedology
authors: Armin Eftekhari, Han Lun Yap, Michael B. Wakin, Christopher J. Rozell
year: 2018
title: 'Stabilizing Embedology: Geometry-Preserving Delay-Coordinate Maps'
doi: 10.1103/PhysRevE.97.022222
url: https://arxiv.org/abs/1609.06347v2
claim: Stable delay embeddings require quantitative geometry beyond injectivity; the conclusions pose a measurement-design question about increasing stable rank.
strata_touched:
  - D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel
license: citation-only
triage: anchor
---

# Stable observation and the measurement-design question

Eftekhari, Yap, Wakin, Rozell, *Physical Review E* 97, 022222 (2018).
DOI and authors were checked against the publisher's record.

## Exact source locators

The publisher accepted manuscript, Section III.A, assumptions A1–A3 and
Equations (14)–(16), defines a finite basis family H and the stable rank of
trajectory difference matrices. A scalar sensor is subsequently selected as
h_alpha = alpha^T H. The stable-rank quantity in Equation (16) depends on the
basis family H, not on alpha within a fixed family.

Section V, the second open-problem bullet (accepted manuscript printed page
34), asks whether optimizing measurement functions can increase stable rank.
The authors express a negative expectation in that paragraph. Their main
stable-embedding theorem additionally controls geometric quantities such as
bi-Lipschitz constants and reach. Increasing stable rank alone does not certify
all of those conditions.

## Current repository interface

PR #8891, fixed source revision 43af212d7552052567390d48419c48dc05758ad7,
Section 12 of `SYMPLECTIC_PREDICTIVE_COMPLETION.md`, studies a circle rotation
by pi/6 with two delays and designs the whole basis family. It already contains
a four-dimensional comparison, a general separation-margin obstruction and a
ten-dimensional approaching-extremal construction.

Sections 52–54 of `COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md` study the
restricted class of paired sine/cosine harmonics. They prove an upper bound
4/3 for injective families with at most two harmonic pairs, a six-dimensional
three-pair family approaching stable rank 2, and exact chord/noise tradeoffs.
This is a restricted design result, not a solution for arbitrary attractors,
arbitrary smooth sensors, or the original random scalar embedding theorem.
The six-dimensional construction trades fewer basis functions for a worse
separation-margin exponent than the earlier ten-dimensional construction.

The Scribe connection is a literature scope note on the existing observation
kernel document. No new formal theorem is claimed, and the existing Lean
result establishes none of these quantitative stable-rank claims.

## Retrieval record and limitations

On 2026-09-20 the author manuscript arXiv:1609.06347v2 and the publisher accepted
manuscript were read for the definitions and Section V question. The accepted
manuscript text explicitly identifies the basis-family/scalar-sensor distinction.
A screenshot request for its page 34 failed; the question was checked in the
parsed accepted-manuscript text, without claiming a successful visual check.
Repository search for the DOI returned no note. This search result is not an
exhaustive priority determination. The note contains original summary and
precise scope only; no full paper is reproduced.
