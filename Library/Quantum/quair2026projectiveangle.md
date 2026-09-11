---
bibkey: quair2026projectiveangle
authors: QuAIR Team
year: 2026
title: Angular geometry of purified distance
doi: null
url: https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean
claim: The projective angle arccos of the modulus of a pure-vector overlap satisfies the triangle inequality; two assumed displacement bounds give the conditional record-time bound and a finite sum gives the sequential count bound.
strata_touched:
  - D5/S3/QuantumBounds/FubiniStudyRecordTime
license: Apache-2.0
triage: anchor
---

# Projective angle triangle inequality

## Verified locator

The immutable source was retrieved and its complete `projectiveAngle_triangle` proof read:
https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean

`QIT.PureVector.projectiveAngle_triangle` treats finite-dimensional normalized pure vectors.
It rotates the endpoint phases so that the two overlaps with the middle vector are real
and nonnegative, and applies Mathlib's real inner-product angle triangle inequality.
The present module adapts this proof to arbitrary complex inner product spaces and uses
`Complex.exists_norm_eq_mul_self` for the phases. No novelty is claimed for the geometry.

The upstream package pins Lean 4.30.0 and mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; this repository pins Lean 4.33.0 and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, so the package cannot be added as a compatible
Lake dependency. The source copyright remains in the adapted module, and the full license
is retained in `docs/reports/recordtimebound/Lean-QIT-LICENSE.txt`.
The upstream tree contains no NOTICE file. Its original build and transitive axiom closure
were not rerun here; the adapted proof is checked under this repository's pinned kernel.

## Standard conditional consequences

For `record_time_lower_bound`, write d(a,b) = arccos(|<a,b>|) for unit
vectors. Orthogonal endpoints m0 and m1 have d(m0,m1) = pi/2. Symmetry
and the triangle inequality give

    pi/2 <= d(m0,a) + d(a,m1) <= 2 E tau / hbar.

The second inequality uses the theorem's two explicit displacement bounds
from the same initial vector a. Multiplying by hbar > 0 and dividing by
4 E > 0 gives pi hbar/(4 E) <= tau. This is a direct conditional consequence
of the cited geometry, not a separately named theorem in the upstream file.
The phase-alignment proof and its real-angle input apply in an arbitrary
complex inner product space, as in the repository, not only finite dimension.

For `record_count_upper_bound`, apply that inequality to each of N contacts,
with its own a_i, m0_i, m1_i and tau_i, and the same positive E and hbar:

    N pi hbar/(4 E) <= sum_i tau_i <= T,
    N <= 4 E T/(pi hbar).

The finite sum includes N = 0. The sum budget is an explicit hypothesis
representing sequential contacts. Neither consequence derives a physical
speed law or constrains an arbitrary parallel apparatus. In particular,
E is only the positive parameter of the assumed displacement bounds here;
no unproved identification with mean energy or energy variance is made.

## What this note does and does not attest

Attested by this repository's own retrieval: the immutable source linked
in Verified locator and the complete `QIT.PureVector.projectiveAngle_triangle`
proof. The phase alignment and real-angle argument were read, and the two
inequality/summation reductions above were checked against the current Lean
statements. The original geometry citation remains attached to its entry;
the two added citations attest these explicit standard direct consequences.

Not attested here: compilation or the transitive axiom closure of the
upstream package under its original toolchain. This remains
`ASSUMED-UNVERIFIED`; the repository's adapted module has its own kernel
report. No Hamiltonian evolution or Mandelstam–Tamm derivation was verified
by this note. The physical displacement and contact-budget hypotheses are
inputs, not conclusions established by the cited source.
