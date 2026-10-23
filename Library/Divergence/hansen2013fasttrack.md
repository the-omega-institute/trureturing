---
bibkey: hansen2013fasttrack
authors: Frank Hansen
year: 2013
title: The fast track to Loewner's theorem
doi: 10.1016/j.laa.2013.01.022
url: https://arxiv.org/abs/1112.0098
claim: A block sandwich shows that operator monotonicity on a doubled space yields operator concavity on the original space.
strata_touched:
  - D5/S3/Quantum/Lieb
license: citation-only
triage: anchor
---

# Monotonicity to concavity through a block sandwich

Frank Hansen, *The fast track to Loewner's theorem*, Linear Algebra and its
Applications 438 (2013), 4557–4571, DOI
<https://doi.org/10.1016/j.laa.2013.01.022>.
The opened source is arXiv:1112.0098v3, Theorem 2.1 and its proof.
No mathematical literature novelty is claimed.

The local theorem
`D5.S3.Quantum.Lieb.MonotoneBlockConcavity.monotone_double_space_concavity`
retains continuity on the positive half-line as an explicit hypothesis.
Its operators are actual bounded operators on an arbitrary complete nontrivial
complex Hilbert space H. Monotonicity is required on H + H; concavity is proved
on H for strictly positive inputs and every real weight in [0,1]. There is no
finite-dimensionality or finite-spectrum restriction.

The proof rotates diag(A,B), dominates its off-diagonal block by a positive
square after adding epsilon I to the first corner and a sufficiently large
scalar to the second corner, applies the operator-monotonicity premise,
compresses to the first corner, and removes epsilon in operator norm through
continuous functional calculus. This is a new local formal proof assembled
from the existing block-operator and Mathlib CFC APIs, rather than a Lean source
transplant.

Hansen also removes the continuity assumption by excluding scalar jumps.
That extra argument, the Bendat–Sherman step and the existence and uniqueness
of a Loewner representing measure are not provided by this module.

## Verified locator

- DOI: https://doi.org/10.1016/j.laa.2013.01.022
- Source: https://arxiv.org/abs/1112.0098
- Opened version: https://arxiv.org/abs/1112.0098v3, Theorem 2.1 and proof,
  pages 3–5.

The bibliographic DOI was verified against the live Crossref record. The opened
arXiv version is preserved in the persistent research source directory.
