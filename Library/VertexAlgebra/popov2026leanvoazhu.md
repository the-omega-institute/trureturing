---
bibkey: popov2026leanvoazhu
authors: Fedor K. Popov
year: 2026
title: Lean_VOA, Modularity/ZhuAlgebraFinite.lean
doi: null
url: https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean
claim: C2 cofiniteness implies finite-dimensionality of the Zhu quotient by homogeneous generators and strict energy descent.
strata_touched:
  - D5/S3/VertexAlgebra/Lattice/ActualZhuFinite
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/popov2026leanvoazhu -->

# Finite-dimensional Zhu quotient from C2 cofiniteness

## Verified locator

<https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>

Fedor K. Popov's pinned source proves
`VOA.finiteDimensional_A_of_C2Cofinite` using finite homogeneous
C2 representatives, absorption of the leading minus-two mode by the full
circle sum, and induction on energy. This is a literature-attested result,
not a claim of independent mathematical novelty. The pinned file has SHA256
`45135c0462f3f274b14a47c03ca2d2e9ef31a1d09b91f9a1033f3699dbca678d`.

The local source-faithful port consumes the existing actual lattice C2
cofiniteness theorem. It replaces the upstream carrier and grading with the
repository's original `Carrier D`, coefficient-filter energy projections,
and existing full `NormFourZhuFinite.circle`. Fixed-energy C2 projection
expands both unrestricted inputs into finite homogeneous sums; only pairs
with energy sum plus one equal to the target energy survive. The remaining
circle terms have strictly smaller energy, so homogeneous finite lifts
span the original carrier modulo the full `zhuO D`.

## Port and retirement

The upstream pin uses Lean v4.30.0 and mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; this repository uses Lean
v4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
These distinct pins exclude the dependency form under SPEC A17.2; the
source-faithful port retains Fedor K. Popov's copyright and Apache-2.0
attribution. The repository root LICENSE supplies the full Apache-2.0
terms; the pinned upstream tree has no additional NOTICE or COPYING file.

Retire the local proof port when this repository's own pinned mathlib
contains an equivalent C2-cofinite-to-Zhu-finite theorem and an actually
compiled exact carrier, grading and O-space bridge makes the full local
statement a direct application. Replace the port with that supplier at
that point. This condition is currently unmet and does not depend on
upstream acceptance by mathlib.

## Scope and audit boundary

The local theorem covers all original charge and oscillator states and
rank zero, under positive-definiteness of the real Gram matrix. It assumes
neither `C2 <= zhuO` nor gradedness of `zhuO`. The O-space uses every full
circle generator, with arbitrary second input; the restricted norm-four
O-space is not identified with this full O-space. The result asserts only
finite-dimensionality of the additive quotient. Zhu multiplication,
rationality, analytic CFT, fusion, anomaly, string theory and AdS/CFT remain
separate obligations.

Four-slot escape registration for
`positive_definite_zhu_quotient_finite` remains unfinished. The source-owner
mirrors do not supply a faithful enrolled readout with compiled original
statement reconstruction, law bridge, whole-family variation, sensitivity,
actual observational dependence and source-selection/realization evidence.
[#28685](https://github.com/the-omega-institute/trureturing/issues/28685)
also covers the exposed projection and nonnegative-support helpers if the
public-declaration delta selects them. They are reused supplier proofs,
not new escape-content claims. The linked-issue route under CLAUDE §3.9
does not establish `declared_validated`. Issue #28628 concerns the earlier
C2 theorem and does not register this result.
