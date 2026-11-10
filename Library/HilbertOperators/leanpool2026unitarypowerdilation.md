---
bibkey: leanpool2026unitarypowerdilation
authors: Ezzeri Esa
year: 2026
title: Halmos and common-all-powers unitary dilation on arbitrary complex Hilbert spaces
doi: null
url: https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/LeanPool/OperatorTheory/Operator/Dilation/Schaeffer.lean
claim: Every contraction on an arbitrary complete complex Hilbert space admits one inner-product-preserving embedding into one complete complex Hilbert space and one unitary whose every natural power compresses to the corresponding power of the contraction.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Common unitary dilation of all natural powers

For every universe `u`, complete complex Hilbert space `E : Type u`, and
continuous complex-linear operator `T` on `E` with `norm(T) ≤ 1`, there exist
`H : Type u`, complete complex Hilbert structures on `H`, a continuous
complex-linear map `V : E → H` preserving every inner product, and one
unitary bounded operator `U` on `H`, such that
`adjoint(V)((U^n)(V(x))) = (T^n)(x)` for every natural `n` and every `x : E`.
The same `H,V,U` serve every power. Zero spaces and `n = 0` are included;
there are no dimension, separability, basis or nontriviality premises.

The formal attestation for this full scope is the actual source theorem
`exists_unitary_power_dilation`, not a finite-dimensional dilation theorem.
The native endpoint with the same name is in
`D5/S3/HilbertOperators/UnitaryPowerDilation.lean`, namespace
`D5.S3.HilbertOperators.UnitaryPowerDilation`.
This is known classical mathematics reused from an existing formal proof,
with no mathematical originality or open-problem resolution claim.

The construction uses the Hilbert sum
`lp (fun _ : Int => WithLp 2 (E × E)) 2`. A Halmos unitary acts at every
system-environment site, then only the environment output is routed one
site right. The joint induction establishes the first coordinate `T^n x`,
a zero second coordinate at site zero, and zero at every negative site.
The latter two assertions propagate the first at the successor step.
The source's use of `Complex.I` is complex-specific. No arbitrary `RCLike`
extension, minimality, uniqueness, effective construction or finite
environment conclusion is supplied.

## Immutable source correspondence

The selected source revision is `LeanPool/lean-pool` at
`89f2facbb6478492222a9b43047e9c837bc65be6`.
Both source and host use Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The source import closure outside Mathlib consists of just these two files:

| Source file | SHA-256 | Retained source section |
| --- | --- | --- |
| [Halmos.lean](https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/LeanPool/OperatorTheory/Operator/Dilation/Halmos.lean) | `9e2941a526ebdb6a8b06742263ff8451205c492fd82d992dcf0c913c55994e2a` | Lines 32–184: off-diagonal contraction, grading and square-root coordinate argument, flip, and `exists_halmos_unitary_dilation`. |
| [Schaeffer.lean](https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/LeanPool/OperatorTheory/Operator/Dilation/Schaeffer.lean) | `c770c8e2e25f6b77e48661854b2fa5ae89f0752a6488b109de6fdb3c5fc2ef65` | Lines 148–509: network fibers, embedding, pointwise interaction, routing, orbit, joint `schaeffer_power_state` induction and the original all-powers endpoint; unused definitional application helpers are omitted. |

Modification notice: the selected sections are combined in one native module
and namespace, imports are changed from public source-module imports to
ordinary Mathlib imports, module/expose wrappers are removed, and every
support declaration is private. The unused simple `SchaefferSpace`, its
embedding, generic `lpReindex` and bilateral-shift branch (source lines
37–147) are omitted. The unused definitional application lemmas
`schaefferFiberEmbedding_apply`, `halmosGrading_apply`, `halmosFlip_apply`,
`schaefferNetworkEmbedding_apply`, `lpPointwiseForward_apply`,
`schaefferRouteForward_apply` and `schaefferRouteBackward_apply` are omitted.
Their source definitional equalities remain inline at their original uses;
the network embedding still has its original definitional proof.
The endpoint telescope, repeated-interaction construction and substantive
proof steps are preserved. No external Lake dependency is added.

## Copyright, license and notice chain

Both selected proof files carry this complete original notice, retained
separately with the source-section mapping in the combined Lean file:

```text
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
```

The complete Pool [LICENSE](https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/LICENSE)
is reused at `docs/reports/brooks-suppliers/lean-pool-LICENSE.txt`:
11,358 bytes, SHA-256
`c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`.
The exact full Pool [NOTICE](https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/NOTICE)
is retained at `docs/reports/unitary-power-dilation-suppliers/lean-pool-NOTICE.txt`:
38,432 bytes, SHA-256
`d17b68e65d4242f88f3bd41eb8a58eba7e512b0d32edd197eb812ef69447fda1`.
The exact full [NOTICE.extra.yml](https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/NOTICE.extra.yml)
is retained with its original filename identified here at
`docs/reports/unitary-power-dilation-suppliers/lean-pool-NOTICE.extra.yml.txt`:
8,557 bytes, SHA-256
`41b9d8eeedee68df9f184965d831c57b9d29f0ea9d3932517b84c7bdd8d81465`.

The Pool provenance identifies the ancestor
[savarin/lean-operator-theory](https://github.com/savarin/lean-operator-theory/tree/6f90bb7e6b056b54f56005e0416d77d6d7c2a478)
at `6f90bb7e6b056b54f56005e0416d77d6d7c2a478`. Its complete Apache-2.0
[LICENSE](https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/LICENSE)
is reused at `docs/reports/brooks-suppliers/daviskahan-LICENSE.txt`:
11,357 bytes, SHA-256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.

The classical reference is J. J. Schäffer, *On unitary dilations of
contractions*, Proceedings of the American Mathematical Society 6 (1955),
322, [DOI 10.1090/S0002-9939-1955-0068740-7](https://doi.org/10.1090/S0002-9939-1955-0068740-7).
The original AMS PDF was unavailable with HTTP 403 and was not compared;
no original-paper page-to-proof correspondence is asserted. The full
arbitrary-Hilbert statement and this particular construction are attested
by the formal source above.

Retirement is determined by this repository's actually adopted Mathlib pin:
when that pin contains an equivalent full arbitrary-complete-complex-Hilbert
common-all-powers theorem, replace the transplanted endpoint by direct
reuse and remove support made redundant by that supplier. Acceptance into
some other upstream revision alone does not meet this condition.

## Locator

https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/LeanPool/OperatorTheory/Operator/Dilation/Schaeffer.lean
