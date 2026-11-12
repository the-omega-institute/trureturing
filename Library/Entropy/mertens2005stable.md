---
bibkey: mertens2005stable
authors: Stephan Mertens
year: 2005
title: Random Stable Matchings
doi: 10.1088/1742-5468/2005/10/P10008
url: https://arxiv.org/abs/cond-mat/0509221v2
claim: Conjecture 3, equation (15), predicts a single-base exponential probability of solvability on periodic finite-range grids; the present target is precisely d=1,r=2.
strata_touched:
  - D5/S3/Combinatorics/Graph/Roommates/SourceModel
  - D5/S3/Combinatorics/Graph/Roommates/OpenCertificates
license: citation-only
triage: anchor
---

# Range-two cyclic stable partial matchings

Section 2 includes blocking by pairs with one or both vertices single and places
being single last. Section 3.2 uses periodic boundary conditions; equation (12)
gives four neighbors at d=1,r=2. Conjecture 3, equation (15), appears on printed
and PDF page 7 of arXiv v2. Equation (14)'s exclusive-triangle obstruction is
1/864 in this specialization. The published alternative places Conjecture 3 on
printed page 9, PDF page 10.

The verified arXiv PDF is 172239 bytes, SHA-256
7d6324c33a02e44ac9c340d3ddf62964ea6783da61ff2c8b5b56d8afa3a92458.
The alternative is https://www.dcs.gla.ac.uk/~pat/roommates/distribution/papers/mertans.pdf.

The exact specialization is independently explicit at
https://github.com/google-deepmind/formal-conjectures/issues/7849.
Its encoding PR 7854 at dc0fa7334537d8733edceaba09fd88163eeb7cef
contains an unproved target, not a mathematical solution. SourceModel is a
minimal compatibility port of the actual LocalStableMatchings and Roommates
APIs at that revision. It retains N=n+5, involutive permutations with fixed
points for singles, existential solvability, and uniform counts on labelled
profiles. The port's Apache-2.0 notice and full license are retained. No supplier
conjecture proof placeholder is imported. Direct dependency is incompatible:
supplier Lean 4.33.1/mathlib 0df444a360eaa60ab8c11dca51a86af692955474,
project Lean 4.35.0/mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
Retire the port when this project's own pinned Mathlib contains equivalent APIs.

A bounded primary-source and citation screen found no exact solution; this is
not a worldwide openness, novelty or priority guarantee. The independent
complete paper verification of the six-buffer argument is paper-level evidence
only. The exact source probability is the conclusion of
D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result. Its scope is
d=1,r=2, all labelled sizes N>=7, with partial matchings and singles.

## Verified locator

- DOI: https://doi.org/10.1088/1742-5468/2005/10/P10008
- arXiv: https://arxiv.org/abs/cond-mat/0509221v2
