---
bibkey: leanpool2026daviskahanprojector
authors: Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5
year: 2026
title: Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds
doi: null
url: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean
claim: A shared positive two-sided quadratic-form gap for two bounded symmetric operators and their projectable reducing subspaces bounds the operator norm of the projector difference by the perturbation norm divided by the gap, over arbitrary complete RCLike inner-product spaces.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Coercive Sylvester estimates and the common-gap projector bound

The formal source is the five-file slice of `LeanPool/lean-pool` at immutable
revision `bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8`. Its project manifest attributes
`LeanPool/DavisKahan` to
`aiq-kitware/aiq-davis-kahan-1970-rotation-eigenvectgors-perturbation-formalization`
at original revision `38e37da6e147cd0016da1eb05987c3edf7d95b39`.
The authors above are the union of the five selected file headers, including
the human and AI authors exactly as named there; the project-level author
list is not substituted for the per-file credits.

## Statement and scope

The endpoint is `Submodule.opNorm_starProjection_sub_le_of_coercive` in
`D5/S3/HilbertOperators/DavisKahanProjector.lean`. For any `RCLike` scalar field
and any complete normed inner-product space, let `A` and `B` be bounded
symmetric endomorphisms and let `U` and `W` be projectable submodules reducing
`A` and `B`, respectively. Both the subspace and its orthogonal complement
are invariant. For common real `c` and `g > 0`, assume the quadratic forms
of `A` on `U` and of `B` on `W` are at least `(c + g) * norm(x)^2`, while
the forms on their respective orthogonal complements are at most
`c * norm(x)^2`. Then
`norm(U.starProjection - W.starProjection) ≤ norm(B - A) / g`.
All norms of operators are continuous-linear-map operator norms.

The actual selected Lean source quantifies arbitrary `RCLike` scalars and
complete spaces without dimension or separability assumptions. It includes
zero-dimensional and infinite-dimensional spaces, zero and whole subspaces,
and coincident subspaces. There is no finite-rank, equal-rank, simple-eigenvalue,
operator-positivity, nonzero-subspace or small-perturbation premise. The
rectangular Sylvester bounds and algebraic reduced-extension identity do not
assume completeness. The projector geometry and directed estimates do.

The construction combines rectangular coercive Sylvester absorption, the
midpoint shift, reduced extensions, reducing-subspace projection commutation,
and the exact maximum of the two directed projector gaps. This is substantive
known mathematics reused from the cited formal source; neither originality
nor resolution of an open problem is claimed. It does not supply a spectral
measure, a spectral-support-to-form-bound conversion, or a downstream
spectral-localizer or recovery theorem.

Albrecht Seelmann's *Notes on the sin 2 Theta theorem*, arXiv:1310.2036v1,
https://arxiv.org/abs/1310.2036v1, provides contextual operator-angle literature.
Its Theorem 1 assumes a separable Hilbert space and addresses a different
spectral-separation estimate. It is not the attestation for this port's
arbitrary-complete-space or full `RCLike` scope; that attestation is the actual
Lean source below. The original Davis--Kahan 1970 article has not been
inspected here, so no original-paper theorem number or page locator is asserted.

## Source correspondence and attribution

All five selected source files carry the following copyright and release lines:

```text
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
```

Their distinct author lines and correspondence are:

| Selected source within `LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/` | Verbatim author line | Retained declarations and construction |
| --- | --- | --- |
| `Sylvester/Bound.lean` | `Authors: Jon Crall, Claude Fable 5` | `TauCeti.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le`, its private scalar/correction support, rectangular coercive absorption, midpoint-separated bound and operator-norm specialization. |
| `ReducedExtension.lean` | `Authors: Jon Crall, Claude Opus 5` | `TauCeti.re_inner_reducedExtension_self`, the algebraic invariant-subspace quadratic-form identity. |
| `Projection/Gap.lean` | `Authors: Jon Crall, GPT 5.6 High` | `ContinuousLinearMap.norm_add_eq_max_of_block` and `Submodule.norm_starProjection_sub_eq_max`, including the block/Pythagorean and C-star construction. |
| `BoundedOperator/SinTheta.lean` | `Authors: Jon Crall, GPT 5.6 High` | `Submodule.sinTheta_directed_coercive` and the private bounded reduced-extension packaging. |
| `BoundedOperator/Projector.lean` | `Authors: Jon Crall, GPT 5.6 High` | `Submodule.opNorm_starProjection_sub_le_of_coercive`, combining the two directed bounds with the exact maximum identity. |

The complete Apache 2.0 license is retained at
`docs/reports/brooks-suppliers/daviskahan-LICENSE.txt`; the full upstream
LeanPool notice chain is retained at
`docs/reports/brooks-suppliers/daviskahan-NOTICE.txt`. These existing files
apply to the selected source reuse; no unrelated project code is selected.

Modification notice: the port combines these five source units in one module,
expands the upstream quadratic-form and reducing-subspace predicates, adapts
the namespaces and one private helper name, and uses pinned native Mathlib
suppliers for projection, invariance and Pythagorean identities. It preserves
the Sylvester absorption, midpoint, reduced-extension and two-projection
construction and the full endpoint scope.

The selected LeanPool revision uses Lean `v4.35.0-rc3` and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, whereas this port uses Lean
`v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
These different pins preclude a single synchronized Lake dependency.
Retirement is tested against this repository's own future Mathlib pin:
when that pin provides an equivalent declaration, directly reuse it and
retire the redundant port and any support it renders unnecessary.

## Verified locator

The exact common-gap endpoint is in
https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean
as `Submodule.opNorm_starProjection_sub_le_of_coercive`.

The four supporting source units at the same immutable revision are:

- https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/Sylvester/Bound.lean
- https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/ReducedExtension.lean
- https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/Projection/Gap.lean
- https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/SinTheta.lean

Project provenance is given in
https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/projects.yml.
The source license and notice are
https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LICENSE
and
https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/NOTICE.
