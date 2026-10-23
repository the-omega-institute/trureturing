---
bibkey: mathlib2026tracecompactness
authors: Mathlib contributors; Tom Ole Diem
year: 2026
title: Trace ideals, finite orthogonal compression and complete metric compactness
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace
claim: Orthogonal projections are contractions, finite-dimensional normed balls are compact, and closed totally bounded subsets of complete spaces are compact.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/FiniteCompression
  - D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness
license: Apache-2.0
triage: anchor
---

# Trace-norm finite compression

## Verified locator

https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace

## Mathematical suppliers and scope

The pinned Mathlib orthogonal-projection API supplies contractions onto closed
subspaces. Its finite-dimensional normed-space theory supplies compact closed
balls with their inherited norm. Its complete uniform-space theory supplies
compactness from closedness and total boundedness. The trace-class Banach,
ideal-norm, Hilbert-Schmidt and trace-pairing suppliers are the attributed
Tom Ole Diem Physlib development adopted in the corresponding source modules;
the preserved license is `docs/reports/quantum-hs-suppliers/physlib-LICENSE.txt`.

For a positive state rho and an orthogonal projection P onto finitely many
members of a full Hilbert basis, let R=sqrt(rho) and Q=I-P. The discarded
diagonal mass q is the column square sum of RQ. Adjoint invariance gives the
same sum for QR. The column square sum of PR is at most one, and
rho-P rho P=(QR)R+(PR)(RQ). The actual trace-ideal Cauchy-Schwarz estimate
therefore gives trace-norm error at most 2 sqrt(q), without commutation or a
trace-class square root assumption.

For a positive trace-class contraction T, summability of its full native
eigenvalue family makes each threshold set s_i>=exp(-R) finite. Outside the
threshold, singularLog(s_i)>=R, including s_i=0. ENNReal summation gives the
uniform mass estimate q<=M/R for every state in the energy sublevel. No
infinite energy is converted to a real number. Finite compression then gives
total boundedness. Positivity, trace normalization and state-slot energy lower
semicontinuity give closedness, hence trace-norm compactness of the entire
sublevel in the complete trace-class carrier.

These are standard analytic ingredients and their formal combination. No
literature novelty or resolution of the complete common-reference Hamiltonian
problem is claimed. The full Hilbert space may be nonseparable; all zero
eigenvalue fibers and the cases M=0 and an empty sublevel remain in scope.
