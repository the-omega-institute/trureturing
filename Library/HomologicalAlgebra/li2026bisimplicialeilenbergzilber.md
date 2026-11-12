---
bibkey: li2026bisimplicialeilenbergzilber
authors: Jeffrey Li
year: 2026
title: Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy
doi: null
url: https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber
claim: Every bisimplicial object of every abelian category has a chain homotopy equivalence between its total double alternating-face complex and its diagonal alternating-face complex, using the recursive normalized Eilenberg–Mac Lane homotopy.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Bisimplicial Eilenberg–Zilber equivalence

For every pair of independent universe levels `u,v`, every `C : Type u`
with `Category.{v} C` and `Abelian C`, and every
`X : SimplicialObject (SimplicialObject C)`, the source constructs
`HomotopyEquiv (FOne.obj X) (FTwo.obj X)` in `ChainComplex C ℕ`.
Here `FOne` is the total double alternating-face complex, with degree-n
finite coproduct over `p+q=n` and differential `d₁+(-1)^p d₂` on the
`(p,q)` summand. `FTwo` is the alternating-face complex of the diagonal
simplicial object `n ↦ X[n,n]`. Both chain maps and both chain homotopies
are included. No equality of universes, module realization, projectivity,
field, characteristic, additional infinite coproduct, tensor hypothesis,
naturality theorem or monoidal coherence assertion is imposed or supplied.

The normalized equivalence uses the shuffle map as its forward map and
Alexander–Whitney as its inverse. Shuffle followed by Alexander–Whitney
is strictly the identity on the twice-normalized total. The other
composite is homotopic to the diagonal identity by the original recursive
operator `phiOp`. In composition notation `MTwo.comp MOne`, `MOne` acts first.
The recursion is `phiOp(0)=0` and
`phiOp(q+1)=-(phiOp(q)).prime+(hOp(q+1)).prime.comp(D0op(q+1))`.
The all-degree induction proves that
`(phiOp q).comp(boundaryOp q)+(boundaryOp(q+1)).comp(phiOp(q+1))
 +idOp(q+1)-hOp(q+1)` is a structural norm. Its realized Moore retraction
is zero, giving the boundary sign `AW-then-shuffle - identity`.
Transport through the inner and outer normalization comparisons gives the
unnormalized endpoint. This is source receipt of known mathematics,
without a mathematical originality or open-problem resolution claim.

Dold–Puppe's *Homologie nicht-additiver Funktoren. Anwendungen*,
Theorems 2.9 (printed 213) and 2.15 (printed 217), gives the additive
bisimplicial total/diagonal statement and identifies the two maps; see
`doldpuppe1961homologie`. The software retains `Abelian C`.
Eilenberg–Mac Lane's *On the groups H(Π,n), II*, Theorem 2.1a (printed 51),
uses normalized product/tensor quotient chains; see
`eilenbergmaclane1954groupsii`. The software uses Moore kernels.
The classical product or quotient statements and the software normalization
comparison do not by themselves supply the side identities for the received
recursive Moore homotopy. The local universal paired-map cancellation and
Moore-projector proof establish those identities without identifying the
quotient and Moore conventions.

## Immutable source correspondence

The qualified software source is `LeanPool/lean-pool` at
`8bbde3a6de815108d41922c9362ebbe38422663a`, under
`LeanPool/EilenbergZilber`. Its original ancestor is
`jeffrey-dot-li/lean-homology` at
`40c5aae235b0f499ebfc1e68ce574a62b531203c`.
The author's release is
`fd0147a1ffe4f3c14c247574e148893d7cdf8cf6`, LeanPool PR 588:
https://github.com/LeanPool/lean-pool/pull/588 .
The Apache qualification refers to that author-released source and its
Pool notices, not to a blanket license assertion about every file of the
original repository.

| Pool source | SHA-256 | Retained host modules |
| --- | --- | --- |
| `Bisimplicial.lean` | `67a7fd5fa793a64b708aeb1ef1b952961c7d904207e3dd24fe112e838d01b830` | `AlexanderWhitney`, `Bisimplicial` |
| `BisimplicialNormalized.lean` | `b4607d30f502a09fbecf8055c31b00efaf9e747d5fcfa856c9770950feea2afe` | `BisimplicialNormalized` |
| `BisimplicialDerivedOp.lean` | `2fb63012a45baa6bf820eb6aa5f021aa12c49b86a1fbf0be184a306bd2afcca4` | `DerivedOperators`, `NormalizedHomotopy`, `NormalizedOperators`, `RecursiveOperators` |
| `BisimplicialNormalizationComparison.lean` | `28f1d6abb8b8614abe7c402450acca6c23c2b1f7f170de34e5a4e26d27ec1a5e` | `NormalizationComparison` |
| `Shuffle.lean` | `b0230b59a49c7921547afa79fd1d4c7ace20cb38dca64b5b8b19453f3e128b71` | `ShuffleBasic`, `ShuffleDiagonal`, `ShuffleInsertion`, `ShuffleRemoval`, `ShuffleSigns` |

The host modules lie in `D5/S3/HomologicalAlgebra/EilenbergZilber`.
The selected declarations keep their mathematical statements and proof
bodies, up to the receiving identifier spellings and local definitional
exposure in the face, degeneracy and flip calculations. The receiving
namespace, imports and module boundaries differ;
consumed private interfaces are exposed. Unused companion material and
unused reflexive binding declarations are omitted.
Canonical receiving spellings replace F₁/F₂, N₁/N₂ and M₁/M₂ fragments
by FOne/FTwo, NOne/NTwo and MOne/MTwo, and totalMapHomotopy₂ by
totalMapHomotopyTwo. Letter-level realize, prime and comp are
realizeLetter, primeLetter and compLetter; their composition laws use
realizeLetter_compLetter, primeLetter_compLetter and compLetter_assoc.
Each receiving name denotes the single original definition or proof,
without an alias or duplicate implementation. The total-symmetry instance is reused directly from
`HomologicalComplex₂.finiteDegreeTotalSymmetry` in its host owner
`D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.lean`;
that existing implementation is exposed without replacing its proof.
The final two comparison consumers use conventional imports to receive
that conventional host module. There is no extra Lake dependency.

The additional frontal and norm closure is from a separate source snapshot,
`LeanPool/lean-pool` at author release `fd0147a1ffe4f3c14c247574e148893d7cdf8cf6`:

| Pool source | Bytes | SHA-256 | Retained closure |
| --- | ---: | --- | --- |
| `LeanPool/EilenbergZilber/BisimplicialDerivedOp.lean` | 99808 | `1eb49def7e416e4b03613000727ba8d0b792db9a285fcd34349245a19a8fcea9` | `IsFrontalHom`, `primeHom_frontal`, `primeHom_comp_degenZero` in `SpecialContractionShuffle`; operator frontality and norm closure in `SpecialContraction` |

`hOp_horizontal_frontal` is a local calculation for the horizontal shuffle
summands. The local ordered-repeat and signed-shuffle cancellation and
Moore-projector argument establish the three side identities for the
existing recursive normalized homotopy.

## Copyright, license and notice chain

Every received D5 source unit retains its copyright and modification
notice. Scribe exposition adapted from the corresponding source descriptions
carries the same copyright, release and modification notice. The complete
original source header is:

```text
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li
```

The exact Pool legal files are retained in existing admitted locations.
Their full contents, including the Jeffrey Li provenance entries, apply
together with each source header:

| Original file | Retained path | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| LICENSE | `docs/reports/brooks-suppliers/lean-pool-LICENSE.txt` | 11358 | `c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c` |
| NOTICE | `docs/reports/unitary-power-dilation-suppliers/lean-pool-NOTICE.txt` | 38432 | `d17b68e65d4242f88f3bd41eb8a58eba7e512b0d32edd197eb812ef69447fda1` |
| NOTICE.extra.yml | `docs/reports/unitary-power-dilation-suppliers/lean-pool-NOTICE.extra.yml.txt` | 8557 | `41b9d8eeedee68df9f184965d831c57b9d29f0ea9d3932517b84c7bdd8d81465` |

Retirement requires an equivalent supplier in the host's actually pinned
Lean library, with the same arbitrary abelian-category scope, independent
universes and full chain homotopy equivalence. Migrate consumers to that
supplier by direct reuse and the canonical migration route before
retiring redundant transplanted material. Acceptance in a different
upstream revision alone does not meet this condition.

## Verified locator

https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber
