---
bibkey: tauceti2026squarerootarithmetic
authors: The Tau Ceti contributors, Chris Birkbeck
year: 2026
title: Square-root Galois extensions and arithmetic Frobenius in TauCeti
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/Multiquadratic/Galois/Basic.lean
claim: The Galois construction and local Frobenius calculation are attributed proof adaptations; the receiving unrestricted unramifiedness theorem is a local deduction from attributed primitives, without an authenticated exact external theorem locator.
strata_touched:
  - D5/S3/Factorization/Galois/SquareRootArithmetic
license: Apache-2.0
triage: anchor
---

# Square-root arithmetic: source attribution and scope

The receiving module is `D5.S3.Factorization.Galois.SquareRootArithmetic`.
Its accepted source has SHA-256
`aabfa33cc8bd79db0e337bbbf0441d3ebfd4435185c8839cba02d17a134a8cda`
and 22,004 bytes. The source attribution below is to TauCeti revision
`14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d`; the receiving mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. TauCeti is not a receiving
manifest dependency. These are source adaptations using the existing imports.

## Verified locator

Primary immutable source:
https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/Multiquadratic/Galois/Basic.lean

- [TauCeti.Multiquadratic.isGalois, lines 187–205](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/Multiquadratic/Galois/Basic.lean#L187-L205).
- [TauCeti.Multiquadratic.isSplittingField, lines 159–176](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/Multiquadratic/Galois/Basic.lean#L159-L176).
- [AlgHom.IsArithFrobAt.apply_sqrt, lines 101–119, with its helpers at lines 51–94](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/LegendreSymbol/Frobenius.lean#L51-L119).
- [NumberField.isArithFrobAt_apply_sqrt, lines 150–158](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/NumberField/Frobenius.lean#L150-L158).
- [TauCeti.IntermediateField extensionality, lines 92–116](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/FieldTheory/IntermediateField/Adjoin/EqTop.lean#L92-L116).
- [NumberField.integralSqrt and its identities, lines 57–70](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/NumberField/IntegralSqrt.lean#L57-L70).
- [NumberField.RingOfIntegers.smulCommClass, lines 98–105](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/NumberField/AutomorphismAction.lean#L98-L105).
- [Related squarefree unramifiedness theorem, lines 95–105](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/TauCeti/NumberTheory/Multiquadratic/RamifiedPrimes.lean#L95-L105).
- [Upstream Apache-2.0 license](https://github.com/TauCetiProject/TauCeti/blob/14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d/LICENSE).

## Declaration correspondence

`squareRootAdjoin_isGalois` (receiving lines 139–157) is the upstream
`TauCeti.Multiquadratic.isGalois` statement and proof after renaming the theorem.
Both retain arbitrary fields `K`, `L`, an algebra structure, an arbitrary finite
index type, the equations `root i ^ 2 = algebraMap K L (d i)`, and
`[NeZero (2 : K)]`. The empty family and zero radicands remain allowed.
Normality comes from the splitting field of the product of quadratic factors;
the separability proof separately handles a zero radicand. The supporting
`isSplittingField` proof is textually identical after changing visibility to
private. The other generator and polynomial helpers follow the same upstream
file at lines 61–176. This is an attributed adaptation, without a novelty claim.
Upstream's own provenance paragraph at lines 39–44 credits a generalization of
the concrete-field work in `kim-em/erdos-unit-distance`; this note does not claim
an independently checked earlier revision or priority chain.

`arithmeticFrobenius_sqrt` (receiving lines 339–356) adapts the two Frobenius
sources above. The receiving private `frobenius_apply_sqrt` proof at lines
294–312 is textually identical to `AlgHom.IsArithFrobAt.apply_sqrt` after its
private name and one helper qualification are changed. The congruence and sign
separation helpers at lines 244–287 follow upstream lines 51–94. The integral
root packaging follows `IntegralSqrt.lean`; the private scalar-commutation
instance specializes `AutomorphismAction.lean` to the rational base.

The public receiving statement has `IsArithFrobAt (𝓞 ℚ) σ Q` and conclusion
`σ x = jacobiSym d p • x`. The upstream number-field theorem instead has
`IsArithFrobAt ℤ σ Q` and `legendreSym p d • x`. Receiving lines 317–335 use
`Rat.ringOfIntegersEquiv` to transport the base residue cardinality, and line
356 converts the Legendre symbol to the Jacobi symbol. Both formulations only
require a characteristic-zero field, an odd prime not dividing the radicand,
and an ideal above that prime; no `NumberField K` or `Q.IsPrime` assumption is
added to this Frobenius statement. The source correspondence is a proof port
with explicit receiving bridges, rather than an assertion of identical full
telescopes.

`squareRoot_unramified` (receiving lines 393–418) is a local deduction in the
accepted candidate. Its finite family of integer radicands need not be
squarefree or independent. Chosen square roots generate the whole number
field; `p` is odd and avoids every radicand; `Q` is a prime above `(p)`. Its
conclusion is `Algebra.IsUnramifiedAt (𝓞 ℚ) Q`.

The existing proof first obtains Galoisness from the attributed Galois
construction. Its local helper `apply_eq_self_of_mem_inertia` (lines 360–388)
uses `Ideal.mem_inertia`, the two possible signs of a square root, integrality,
primality of `Q`, and the lies-over divisibility test to exclude the negative
sign. The attributed extensionality helpers then show that inertia is trivial.
Finally the receiving mathlib primitives
`Ideal.card_inertia_eq_ramificationIdxIn`,
`Ideal.ramificationIdxIn_eq_ramificationIdx`, and
`Ideal.ramificationIdx_eq_one_iff` yield unramifiedness. This describes the
accepted proof's dependencies; it introduces no new proof or originality claim.

The related upstream theorem
`TauCeti.Multiquadratic.isUnramifiedIn_iff_forall_not_dvd_of_ne_two` explicitly
assumes `∀ i, Squarefree (d i)` and concludes a global `IsUnramifiedIn` statement
over `ℤ`. Its proof passes through ramified primes and fundamental
discriminants. It is not an authenticated exact source for the receiving
unrestricted, pointwise telescope. No exact external declaration or proof
match for that unrestricted theorem was authenticated in this bounded review.

## Supporting helper attribution

All 26 helpers remain consumed support, without independent credit. The ten
Galois helpers from `definingPolynomial` through `isSplittingField` correspond
to the upstream Galois file; the three extensionality helpers correspond to
`EqTop.lean`; the three integral-root helpers correspond to
`IntegralSqrt.lean`; the scalar instance adapts `AutomorphismAction.lean`; and
the three local Frobenius helpers correspond to the Legendre-symbol file.
The two rational-base cardinality bridges and the inertia-fixation helper
are local steps visible in the receiving proof.

The defining files of the imported polynomial-splitting primitive and the
integer lies-over membership/cardinality primitives were not opened in the
accepted bounded provenance review. Their dependencies are visible in the
inspected imports and calls, but exact textual identity of those three
receiving primitive-helper proofs is not certified here. No additional
defining locator or priority claim is asserted.

## License and distribution

The inspected upstream source headers state:

> Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: The Tau Ceti contributors

`EqTop.lean` additionally names Chris Birkbeck among its authors. Retain those
notices and the receiving source's prominent adaptation/revision notice.
Distribute the complete upstream license at `licenses/TauCeti-LICENSE`, the
path named by the receiving header. The exact supplied license has 11,357
bytes and SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
Apache-2.0 section 4 requires a license copy, prominent notices of modification,
retention of applicable source attribution notices, and retention of applicable
NOTICE attribution when supplied. The upstream root tree has no `NOTICE` file
at this revision. The complete license text is distributed at that receiving path.

This note supplies source attribution and scope. It does not establish current
canonical admission, an elaborated equivalence, registration completion, or
research novelty. Retire source ports when the receiving pinned library
provides the corresponding statements and the actual consumers can reuse them
directly under the ordinary validation gates.
