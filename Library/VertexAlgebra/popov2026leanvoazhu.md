---
bibkey: popov2026leanvoazhu
authors: Fedor K. Popov
year: 2026
title: Lean_VOA, full Zhu quotient algebra and original-carrier residue laws
doi: null
url: https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean
claim: C2 cofiniteness gives finite Zhu additive quotient; higher-circle recursion and weighted commutator collapse give right-argument O stability; two finite higher-circle towers express the full actual associator in O; translation residues give left-argument O stability and the nonzero finite-dimensional unital complex quotient algebra.
strata_touched:
  - D5/S3/VertexAlgebra/Lattice/ActualZhuFinite
  - D5/S3/VertexAlgebra/Lattice/ActualZhuBinomial
  - D5/S3/VertexAlgebra/Lattice/ActualZhuProduct
  - D5/S3/VertexAlgebra/Lattice/ActualZhuRightIdeal
  - D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity
  - D5/S3/VertexAlgebra/Lattice/ActualZhuAssociatorScalar
  - D5/S3/VertexAlgebra/Lattice/ActualZhuAssociatorExpansion
  - D5/S3/VertexAlgebra/Lattice/ActualZhuAssociator
  - D5/S3/VertexAlgebra/Lattice/ActualZhuLeftIdeal
  - D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra
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
O-space is not identified with this full O-space. The finite-quotient theorem asserts finite-dimensionality of the additive
quotient. The associator and quotient-algebra constructions below supply
two-sided Zhu descent and associativity separately. Rationality, analytic
CFT, fusion, anomaly, string theory and AdS/CFT remain separate obligations.

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
The positive-definite right-stability theorem includes rank zero and
arbitrary original charge and oscillator states. It proves `star u o ∈ O`
for `o ∈ O`. The associator, opposite-argument stability and quotient
Ring/Algebra constructions are supplied separately below.

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

## Full original-carrier associator

The same immutable revision supplies
[ZhuMuIdentity.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuMuIdentity.lean),
[ZhuUCore.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuUCore.lean),
[ZhuVCore.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuVCore.lean), and
[ZhuAssociator.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuAssociator.lean).
Their respective SHA256 values are
`d5331d266fde48898921d23a276b1ced5af9d39e46f52132fea357543797385d`,
`91a719766953e94b3b7c227dff738b8e52639c76b5fead2a645c158ab6d61198`,
`1c678f98391c0a8e6b921bccb23b823fb9d10785a7fa787478044437d806fb3c`, and
`733725cca0c4ac72112b440392242d853378e35a7db197e80e5518d2591f468f`.
The differing Lean/mathlib pins and Apache-2.0 attribution above apply to
these source-faithful native ports as well; no independent mathematical
novelty is claimed.

`ActualZhuAssociator.associator_mem_zhuO` states, for every original lattice
datum `D`, positive-definiteness of its real Gram matrix, and arbitrary
`u v w : Carrier D`, that
`star D (star D u v) w - star D u (star D v w)` belongs to the literal
`ActualZhuFinite.zhuO D`. All charge and oscillator states and rank zero
remain included. Neither associativity nor either O-stability theorem is
assumed for this conclusion.

For homogeneous `u,v` of natural weights `K,L`, regularity bounds the inner
nonnegative modes by finite ranges `Bu` and `Bv`. The native all-state
iterate and its two finite-support families expand the left associated
product. The private U/V kernels and `mu_identity` identify its residual
with `Ufam + Vfam`: the U tower is the sum over `b < Bv` and `n ≤ b` of
`muCoeff L b n` times `higherCircle D K u (mu D v b w) n`; the V tower is
the sum over `a < Bu` and `n ≤ a` of `muCoeff K a n` times
`higherCircle D L v (mu D u a w) n`. Each term lies in the same literal O
by the existing higher-circle theorem. Finite original energy decomposition
and star bilinearity extend membership to all original `u,v,w`.
All mode indices stay integral, including the `a = 0` iterate's upper
binomial index and exponent `-1`. The scalar helpers are consumed on these
two paths and are not separate mathematical deliveries.

Four-slot escape registration for the public `associator_mem_zhuO` and
`mu_identity` theorems is unfinished under
[#28745](https://github.com/the-omega-institute/trureturing/issues/28745).
Missing evidence comprises faithful typed reconstruction and equivalence
for the complete original telescopes, a lawful enrolled-template readout,
actual-positive law, whole-family intervention and sensitivity, and actual
observational dependence. The associator telescope includes `D`, its
positive-definiteness hypothesis and arbitrary `u,v,w`; the scalar telescope
includes all `K,L,b : Nat` and `s : Int`. Rank-zero, constant and other
degenerate fibres remain in scope. O-membership alone does not prove
nonconstant observational sensitivity, and no `declared_validated`
registration is supplied. Issues #28732 and #28685 retain their distinct
product-chain and finite-quotient scopes.

Opposite-argument O stability, bilinear quotient descent and quotient
Ring/Algebra structure are supplied in the following section. These
algebraic results establish no analytic CFT, fusion, anomaly, string
theory or AdS/CFT statement. Retire these native proofs when an exactly
compiled supplier at the repository's pinned versions supplies the same
full-carrier, literal-O statement and integer-boundary identities.

## Full quotient algebra

At the same immutable revision,
[ZhuRing.lean](https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuRing.lean)
supplies the quotient ring construction. The native
`ActualZhuLeftIdeal` proves the translation residue identity and
left-argument stability on the original full circle span.
`ActualZhuAlgebra` descends the original star through both proved ideal
stabilities and obtains associativity and vacuum units from the native
associator and creation laws. Grade-zero projection annihilates every
literal circle while retaining the nonzero vacuum; this does not assert
gradedness of O. Together with the existing
`ActualZhuFinite.positive_definite_zhu_quotient_finite`, the result is a
nonzero finite-dimensional unital complex algebra on exactly
`Carrier D ⧸ ActualZhuFinite.zhuO D` for positive-definite D, including
rank zero. The source attribution, license and distinct version pins above
also apply to this port.

The dependent-family audit for `translation_star_circle`,
`star_left_mem_zhuO`, `quotientProduct_mk` and `vacuum_not_mem_zhuO`
remains incomplete: exact reconstruction, an enrolled readout,
the actual-positive law, whole-family variation and sensitivity,
actual observational dependence and current source binding are required;
see <https://github.com/the-omega-institute/trureturing/issues/28745>.
