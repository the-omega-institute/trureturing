---
bibkey: barnett2009discrimination
authors: Stephen M. Barnett and Sarah Croke
year: 2009
title: Quantum state discrimination
doi: 10.1364/AOP.1.000238
claim: Perfect discrimination requires orthogonal state supports, whose number cannot exceed the finite Hilbert-space dimension.
strata_touched:
  - D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity
license: citation-only
triage: anchor
---

# Quantum state discrimination

Barnett and Croke, Advances in Optics and Photonics 1, 238-278 (2009),
review discrimination by positive operator valued measurements. The preprint
is arXiv:0810.1970 (2008).

The literature scope is the standard orthogonality obstruction, specialized
in the Lean theorem to density matrices on a finite complex memory and a
single complete POVM. Section 2 explains why the number of nonzero orthogonal
projectors cannot exceed the state-space dimension. Section 3.2.b treats mixed
states, defines support and kernel, and states that nonorthogonal states need
an inconclusive outcome. The finite-family dimension bound combines these
facts; this note does not attribute a separately numbered history-capacity
theorem or any repository-specific history terminology to the paper.

The local Lean proof converts trace pairings to range/kernel containment,
then selects nonzero orthogonal vectors. It imports only pinned Mathlib.
The related Lean result `HermitianMat.inner_zero_iff` and its private
`inner_zero_iff_aux_lemma` were found in
`leanprover-community/physlib`,
`QuantumInfo/ForMathlib/HermitianMat/Inner.lean`, commit
`6a09b2d1761a0d4430083045a247eb121d8da260`.
Physlib is not an admitted dependency: issue #5555 remains open and its
A17.2 decision concerns a surface outside this implementation lane.
The attempt-2 dispatch expressly authorizes a local proof under rule 11
path 4. This is a literature result, not a mathematical novelty claim.

## Verified locator

- https://doi.org/10.1364/AOP.1.000238
- https://arxiv.org/abs/0810.1970
- https://arxiv.org/html/0810.1970#S2
- https://arxiv.org/html/0810.1970#S3.SS2.SSS2
- Accessed 2026-09-06; title, authors, POVM dimension discussion, and the
  mixed-state support/kernel discussion were read during Stage A.
