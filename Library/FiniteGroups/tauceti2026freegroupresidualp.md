---
bibkey: tauceti2026freegroupresidualp
authors: The Tau Ceti contributors
year: 2026
title: Free groups are residually p
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/GroupTheory/FreeGroup/ResiduallyP.lean
claim: "Every nonidentity element of an arbitrary free group is excluded by a normal subgroup of finite index with p-group quotient, for every prime p."
strata_touched:
  - D5/S3/FiniteGroups/FreeGroup/PrimeQuotientSeparation
license: Apache-2.0
triage: anchor
---

# Residual prime finiteness of free groups

## Exact source attestation

The immutable source revision is
`d91980bdc255e6e50506be147ad9bcb88eb9fcc0` in
[TauCeti](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/GroupTheory/FreeGroup/ResiduallyP.lean).
The source theorem is
`FreeGroup.exists_normal_isPGroup_quotient_notMem`.
It quantifies over arbitrary alphabets, all prime natural numbers, and all
nonidentity words, and gives a normal finite-index subgroup with p-group
quotient excluding the word.

The consumed source files and SHA-256 values are:

- `TauCeti/GroupTheory/FreeGroup/ResiduallyP.lean`:
  `2f6b3657a96f88291eed8087600b30ffa0e9a07febdeacd9d55b3c9691820a08`.
- `TauCeti/GroupTheory/FreeGroup/Syllables.lean`:
  `f69a643c3d4023ef2617d02e3dd24af4ce2b3e4a68520280bb07180ee7f8cbe8`.
- `TauCeti/NumberTheory/Binomial/PadicVal.lean`:
  `9728e935c07c65c1a3be075c4066b3b1e54abe727786497b04d0a7574fb53cde`.

The attribution covers the normal syllable construction, constant-letter
shift powers, binomial entries, valuation weights, and first-row induction.
The short generic-exponent binomial lemma directly applies the pinned Lucas
and integer-valuation lemmas; it is a consumed auxiliary result.

## Adaptation and mathematical scope

The supplier uses Lean 4.36 and Mathlib revision `fc4f59e`; the host uses Lean
4.35 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
This is a faithful attributed adaptation with changed carrier and period,
rather than a claim of token equivalence.
The target is the existing subgroup `NikolovSegal.SLnNormalizer.Uplus`.
The existing `upperChart`, `upperMatrix`, `upperCoordinatesEquiv`, and
`card_Uplus` give the actual matrices, free upper entries, finiteness,
and cardinality. For total word weight D, put n=D+1, q=n(n-1)/2, and K=q+n.
The cardinality p to the q gives the period p to the K used to reduce all
signed integer exponents. Matrix evaluation uses the monoid homomorphism
from this subgroup into matrices. No supplier general linear group,
unipotence, characteristic polynomial, determinant, or matrix inverse
construction is imported.

The syllable exponents remain arbitrary nonzero integers, including negative
and p-divisible integers. Adjacent letters are distinct, and both ends of each
letter run enter the row induction. The resulting quotient is the quotient
by the representation kernel; surjectivity onto the full target is not
asserted. There is no fixed finite observation budget, executable inverse,
or resource bound.

The primary papers of Magnus and Iwasawa cited by the supplier have not been
read here; this note attests the identified formal source and its stated
scope. This adaptation is replaced when equivalent APIs occur in the
repository's pinned Mathlib.

## License

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Apache License, Version 2.0. The full license is retained in
[docs/reports/licenses/TauCeti-LICENSE.txt](../../docs/reports/licenses/TauCeti-LICENSE.txt),
whose supplied SHA-256 is
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The adapted Lean source retains the copyright and license attribution.
