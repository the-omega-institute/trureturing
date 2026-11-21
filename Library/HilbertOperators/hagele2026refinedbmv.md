---
bibkey: hagele2026refinedbmv
authors: Daniel Hägele
year: 2026
title: "On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices"
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
claim: Section 7(iii) leaves the refined BMV lower bound for three occurrences of each matrix open for dimensions at least four.
strata_touched:
  - D5/S3/Quantum/Analysis/RefinedBMV33
  - D5/S3/Quantum/Analysis/RefinedBMVLowerBound
license: citation-only
triage: anchor
---

# The refined BMV lower bound for three letters of each kind

## Verified locator

DOI: 10.48550/arXiv.2611.00129

Source: https://arxiv.org/abs/2611.00129v1

Theorem 1 and Lemma 2 give the known low-dimensional cases and the reduction
from a stronger trace-power comparison. Section 7(iii), page 8, identifies
the higher-dimensional cases with word counts `(3,3)` and `(4,3)`. Sections 3–5 derive the
closed-walk trace expansion and the three-dimensional comparison.

## Scope and conventions

For complex Hermitian matrices `H, K`, take the average of the traces of the
twenty words with three letters `exp H` and three letters `exp K`. The lower
bound is `Tr exp(3H + 3K)`. The mean is real by reversal of the
words and conjugation of their traces.

The four-dimensional proof first shows that the mean for positive
semidefinite `A, B` is at least `Tr((AB)^3)`. Shifting one
matrix by its smallest eigenvalue gives a zero eigenvalue. A symmetric
rational decomposition of the cubic trace defect then groups all walks
at each center into a single quadratic form. The four coefficient
matrices are positive semidefinite by Cauchy and Schur complement
identities. The Schur product theorem preserves each grouped inequality
with complex entries. The dyadic trace-power comparison and Lie–Trotter
give the exponential bound.

The general `(3,3)` proof uses a different symmetric coefficient in the
same cubic trace identity. At each positive spectral center its matrix is
a rank-one positive semidefinite term plus a diagonal congruence of the
Cauchy matrix on the positive eigenvalues. The zero center has only the
Cauchy term. This decomposition gives the product bound in every finite
dimension, and the same trace-power comparison gives the exponential bound.
The symmetric coefficient was found in an independent GPT Pro review, then
checked by exact algebra and used in the formal proof.

- [Hägele, arXiv:2611.00129v1](https://arxiv.org/abs/2611.00129v1).
- [Cha–Lee, the separate upper-bound counterexamples](https://arxiv.org/abs/2603.19927).
