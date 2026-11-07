---
bibkey: atlas2026wold
authors: Meta Platforms, Inc. and affiliates
year: 2026
title: Finite Wold decomposition and residual isometry
url: https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean
doi: null
claim: Finite wandering decompositions with exact Pythagorean identity and the actual residual linear isometric equivalence for arbitrary real or complex inner product spaces.
strata_touched:
  - D5/S3/HilbertOperators/WoldDecomposition
license: upstream LICENSE including intended-use preface; see docs/reports/lovasz-suppliers/atlas-LICENSE.txt
triage: anchor
---

# Finite wandering decomposition and residual equivalence

The supplier is facebookresearch/atlas-lean at immutable revision
`a60759060b5616df0d5775b42da4d337719feb32`, file
`MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean`.
Its SHA-256 is
`8a6fa41461cae3f678ece91c2374ed6ef1d398ca2555b0f32e833a30c4eb3192`.
The supplier and host use Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Equal pins do not establish automatic dependency admission: the A17
predicates remain open. The native module
`D5/S3/HilbertOperators/WoldDecomposition.lean` reuses the necessary source
closure by transplantation under A17.2, without a new Lake dependency or
changes to the pins. Its Blueprint Scribe describes the retained endpoints.

Let k be any RCLike field and H any inner product space over k, with
independent universes, and V a linear isometry H to H. Write
W = (range V) orthogonal and R = infimum over m of range(V^m).
If H is complete, every x and natural n admit a single w : Nat to H and
y : H with all w j in W, w j = 0 for j >= n, and
x = sum over j < n of (V^j)(w j) + (V^n)y and
norm(x)^2 = sum over j < n of norm(w j)^2 + norm(y)^2.
The finite theorem has the conjunction membership AND (support AND
(reconstruction AND norm identity)) for the SAME w and y. Its finite
induction constructs the common coefficient family and remainder, then
applies wold_norm_sq to these data and their reconstruction. The standalone
helper proves the identity for any supplied reconstruction and needs
neither completeness nor finite support. Independently of completeness, V preserves R and its actual
restriction is bijective. The source proves surjectivity by cancellation
of V in successive power-range witnesses, then packages the restriction
as a linear isometric equivalence. Its forward map is literally V.
The zero level and zero spaces are included. There is no assumption of
separability, finite dimension or ambient surjectivity, and no infinite
direct-sum or coefficientwise uniqueness conclusion.

The retained source preserves those arguments, replaces upstream module
wrappers with the native header and namespace, makes consumed support
private and range instances local, removes unused imports, and omits the
unused power-orthogonality, uniqueness, residual-orthogonality and coercion
companion branches. The finite conclusion records both equations by applying
the retained norm helper to the constructed witnesses. This is reuse of a known theorem and its formal proof,
with no original mathematical or proof credit claimed. Historical sources
named by the supplier are H. Wold, A Study in the Analysis of Stationary
Time Series (1938), and P. R. Halmos, Shifts on Hilbert spaces,
Journal fuer die reine und angewandte Mathematik 208 (1961), 102-112.

The full license, including its machine-learning intended-use preface, is
retained at `docs/reports/lovasz-suppliers/atlas-LICENSE.txt`, SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
The source copyright is Meta Platforms, Inc. and affiliates, all rights
reserved. The complete Git tree at the immutable revision contains `LICENSE`
as the only license or notice entry along the source's ancestor chain:
the repository root, `MathlibExt`, `MathlibExt/Analysis`, and
`MathlibExt/Analysis/InnerProductSpace`. This tree fact and the retained
license do not constitute blanket legal clearance. Retire this
transplant when an actually adopted pinned Mathlib revision provides the
equivalent finite support, norm and residual-restriction statements at the
same scope, and directly reuse that Mathlib source.

The special Hardy/finite-Blaschke pure-isometry infinite decomposition in
OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY section 1733 is not asserted to
be this generic finite/residual theorem. It concerns a complex Hardy space,
a finite Blaschke multiplier and an infinite pure-isometry decomposition;
the native statements quantify over arbitrary real or complex inner product
spaces and retain a possibly nonzero residual intersection. No theory-atom
coverage, infinite Hardy decomposition or basis result is claimed here.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean
