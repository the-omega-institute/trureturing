---
bibkey: popov2026leanvoazhu
authors: Fedor K. Popov
year: 2026
title: Lean_VOA, full Zhu quotient and right-ideal residues
doi: null
url: https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean
claim: C2 cofiniteness gives finite Zhu additive quotient; higher-circle recursion and weighted commutator collapse give right-argument O stability.
strata_touched:
  - D5/S3/VertexAlgebra/Lattice/ActualZhuFinite
  - D5/S3/VertexAlgebra/Lattice/ActualZhuBinomial
  - D5/S3/VertexAlgebra/Lattice/ActualZhuProduct
  - D5/S3/VertexAlgebra/Lattice/ActualZhuRightIdeal
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/popov2026leanvoazhu -->

# Finite-dimensional Zhu quotient and original-carrier product

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
finite-dimensionality of the additive quotient. Two-sided Zhu descent and associativity,
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

## Original-carrier product port

The same immutable source revision supplies the residue chain in
[ZhuModule.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuModule.lean),
[ZhuRingResidue.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuRingResidue.lean), and
[ZhuRightIdeal.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuRightIdeal.lean).
Their respective SHA256 values are
`4caf62200c45cd058fdd383be709a5b1c5dfa5fc9d88cbe6690a0741ba790129`,
`d4152184286101cb377ba80e7bb040c571c7808b4a7fb6d6eb52aacae297c894`, and
`c62f18d2b3b493c0db213493dd6778f16e42179255ad12723eb263c76cfe863b`.
The argument is classical Zhu/Frenkel--Zhu mathematics; the Lean proof
source is attributed to Fedor K. Popov under Apache-2.0.
The classical Zhu reference is *Modular invariance of characters of vertex
operator algebras*, JAMS 9 (1996), 237–302,
<https://doi.org/10.1090/S0894-0347-96-00182-8>, also recorded in the existing
[Monster reference note](griess1981monsterlocalcompletion.md). This citation
does not claim a new verification of the classical paper's proof.

The native port constructs star through the existing internal direct sum,
uses the actual state derivative to recurse on higher circle order, and
uses the native all-state mode commutator with its finite nonnegative-product
support. The weighted coefficient identity retains generalized negative
upper binomials through complex-cast integer `Ring.choose`. It acts on the
same literal full `ActualZhuFinite.zhuO`, with an unrestricted second state.
No alternate formal-field stack, representation kernel, associativity or
other-side stability is used. The port's retirement condition is an exactly
compiled supplier of this same full-carrier and literal-O statement at the
repository's pinned versions; a restricted-carrier theorem does not suffice.

The local fields and modes remain `LatticeAllStateField.Y` and
`LatticeAllStateReconstruction.mu`; grading and the internal direct sum
remain supplied by `LatticeEnergyGrading` in the `LatticePositiveEnergy`
namespace, with actual mode grading supplied by `LatticeActualLZeroGrading`.
Translation remains `LatticeSugawaraConformal.translation`, and its mode
derivative is supplied by `LatticeActualStateDerivative`. The original
all-state commutator and `ActualZhuFinite.zhuO`, generated by full
`NormFourZhuFinite.circle` expressions, retain their native ownership.
The positive-definite theorem includes rank zero and arbitrary original
charge and oscillator states. It proves `star u o ∈ O` for `o ∈ O`;
`star o u ∈ O` and `(u star v) star w - u star (v star w) ∈ O` remain
separate missing results. No bilinear quotient product or associative
quotient Ring/Algebra is constructed.

Four-slot escape registration for `ActualZhuBinomial.zhu_right_binom`,
`ActualZhuProduct.star_homogeneous`,
`ActualZhuProduct.higherCircle_mem_zhuO` and
`ActualZhuRightIdeal.star_right_mem_zhuO` is unfinished under
[#28732](https://github.com/the-omega-institute/trureturing/issues/28732).
Missing evidence comprises the full original telescope and scoped readout,
exact source reconstruction and equivalence/law bridge, whole-family
variation, sensitivity, actual observational dependence, source selection
and realization. No faithful compiled `Contract.Registration` or
`declared_validated` status is supplied. Issue #28685 remains specific to
the prior finite quotient and exposed energy helpers; it does not register
these product theorems.
