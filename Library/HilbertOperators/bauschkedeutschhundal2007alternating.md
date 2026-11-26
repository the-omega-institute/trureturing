---
bibkey: bauschkedeutschhundal2007alternating
authors: Heinz H. Bauschke, Frank Deutsch, Hein Hundal
year: 2007
title: Characterizing arbitrarily slow convergence in the method of alternating projections
doi: null
url: https://arxiv.org/pdf/0710.2387v1
claim: For two closed linear subspaces of a real or complex Hilbert space, the actual projection-product powers converge in norm on each vector to the intersection projection.
strata_touched: []
license: arXiv assumed-1991-2003; citation only
triage: anchor
---

# Alternating orthogonal projections

Theorem 1.1 on printed page 1 of arXiv:0710.2387v1 states the classical
von Neumann two-subspace strong convergence theorem. The ambient Hilbert
space is real or complex, the subspaces are closed and linear, and the
conclusion concerns the unaveraged projection-product powers on every
vector. No positive Friedrichs angle, finite dimension, separability or
convergence rate is required. Theorem 1.2 and the following discussion
concern additional operator-norm and rate statements, which are distinct
from pointwise strong convergence.

C. Badea, S. Grivaux and V. Müller, *The rate of convergence in the method
of alternating projections*, arXiv:1006.2047v1, equation (1.1) on page 1,
also states the strong convergence formula; its subsequent discussion
distinguishes convergence in operator norm and angle-dependent rates.

The Lean proof uses the pinned Mathlib orthogonal-projection and mean
ergodic theorems directly. Projection energy gives asymptotic regularity.
A fixed finite averaging window then transfers Cesàro convergence to
convergence of the actual powers. This is a proof of established
mathematics. The citations supply the classical statement; no external
Lean source or article text is copied, and the original von Neumann
publication is not the source of a direct quotation here.

## Verified locator

https://arxiv.org/pdf/0710.2387v1, printed page 1, Theorem 1.1: the
classical von Neumann two-subspace strong convergence theorem for closed
linear subspaces of a real or complex Hilbert space.
