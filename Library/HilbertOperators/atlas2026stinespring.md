---
bibkey: atlas2026stinespring
authors: Meta Platforms, Inc. and affiliates
year: 2026
title: Stinespring dilation for arbitrary completely positive maps
url: https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/CStarAlgebra/Stinespring.lean
doi: null
claim: Every completely positive map from a unital complex C*-algebra to bounded operators on a complex Hilbert space has a same-universe Hilbert-space star-representation dilation with bounded compression map.
strata_touched:
  - D5/S3/HilbertOperators/Stinespring
license: upstream LICENSE including intended-use preface; see docs/reports/lovasz-suppliers/atlas-LICENSE.txt
triage: anchor
---

# Generic Stinespring dilation

The formal supplier is facebookresearch/atlas-lean at immutable revision
`a60759060b5616df0d5775b42da4d337719feb32`, file
`MathlibExt/Analysis/CStarAlgebra/Stinespring.lean`.
The source has 37,000 bytes and 734 lines, SHA-256
`0910650fe26746abe5689911e2d48c7cdff9a10882d71682ff136fccae26fa39`,
and Git blob `e393ebe1e0ab70219d6ca7da1eb0835538266b45`.
Its endpoint is
`MathlibExt.Analysis.CStarAlgebra.StinespringWanted.stinespring_dilation`.
The supplier and host use Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Equal pins do not establish dependency admission: the A17 predicates remain
open. The native module reuses this leaf proof by narrow source transplant
under A17.2, with no new Lake dependency. Its ten imports are Mathlib modules.
The native header and namespace replace the source module/public wrappers;
source-local numbering comments are omitted. Mathematical statements and
proof bodies are preserved.

For every universe u, let A and H be types in Type u. Assume CStarAlgebra A,
PartialOrder A, StarOrderedRing A, NormedAddCommGroup H,
InnerProductSpace Complex H and CompleteSpace H. For every completely
positive linear map phi from A to bounded complex-linear operators on H,
there exist K in Type u, its normed additive group, complex inner product
and completeness structures, a unital complex star-algebra homomorphism pi
from A to bounded operators on K, and a bounded complex-linear map V from
H to K such that phi(a)(x) = adjoint(V)(pi(a)(V(x))) for every a and x.
These are common witnesses for all a,x. No finite dimension, separability,
unitality of phi or trace preservation is assumed. No isometry, minimality
or uniqueness conclusion is asserted.

The proof constructs a positive semidefinite sesquilinear form on finitely
supported functions from A to H. Complete positivity supplies positivity
of the operator-valued Gram matrices; positive-cone closure induction
establishes their nonnegative quadratic forms. The separated completion
is the Hilbert space K. The bound for left multiplication by c is norm(c),
which gives the continuous representation. The vector map supported at
the algebra unit has bound sqrt(norm(phi(1))). Its inner-product identity
with the representation gives the compression formula by adjointness.
This construction extends the native object class beyond finite Kraus
representations and the explicit Fock attenuator family. It supplies a
general operator representation, without claiming a recovery theorem,
finite environment, tensor factorization or arithmetic gluing result.

The mathematical source is W. Forrest Stinespring, "Positive functions on
C*-algebras", Proceedings of the American Mathematical Society 6 (1955),
211-216, DOI `10.1090/S0002-9939-1955-0069403-4`. Crossref's publisher record
identifies the title, author, volume and pages; its alternative JSTOR record
is DOI `10.2307/2032342`. The formal proof is supplied by the immutable Atlas
source above. This is known mathematics and reuse of its existing formal
proof, with no mathematical originality claim.

The full upstream license, including its machine-learning intended-use
preface, is retained byte for byte at
`docs/reports/lovasz-suppliers/atlas-LICENSE.txt`, SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
The original copyright notice is retained in the Lean source. The approved
immutable-tree source screen identified the root LICENSE as the only
applicable license or notice along the ancestor chain. This is mathematical
theorem-library use. The source and license evidence do not constitute a
blanket legal-clearance claim.

Retire the transplant and directly reuse equivalent declarations when the
host actually adopts a pinned Mathlib revision providing this same generic
completely positive dilation, with arbitrary unital C*-algebra and Hilbert
space and no additional hypotheses on phi.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/CStarAlgebra/Stinespring.lean

Original mathematical paper: https://doi.org/10.1090/S0002-9939-1955-0069403-4
