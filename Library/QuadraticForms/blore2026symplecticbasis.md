---
bibkey: blore2026symplecticbasis
authors: Zayn Blore
year: 2026
title: Symplectic bases of alternating bilinear forms in CsdLean4
doi: null
url: https://github.com/zblore/csd-lean4/blob/39182b9e91a2791f5acb5ceaa2612ed71da921b5/CsdLean4/Mathlib/LinearAlgebra/BilinearForm/SymplecticBasis.lean
claim: Every finite-dimensional nondegenerate alternating bilinear form over a field has a symplectic basis, including dimension zero.
strata_touched:
  - D5/S3/QuadraticForms/SymplecticBasis
license: Apache-2.0
triage: anchor
---

## Verified locator

URL: https://github.com/zblore/csd-lean4/blob/39182b9e91a2791f5acb5ceaa2612ed71da921b5/CsdLean4/Mathlib/LinearAlgebra/BilinearForm/SymplecticBasis.lean

The immutable source revision is 39182b9e91a2791f5acb5ceaa2612ed71da921b5.
The source SHA-256 is
0aad253cae916206016ca59cdfe15c23a113dc84c78636551f69e3677d1add36.
The source credits Copyright (c) 2026 Zayn Blore. All rights reserved.
The complete license at that revision is byte-identical to
[the retained Apache-2.0 license](../../docs/reports/qmutualinfo/csd-lean4-LICENSE.txt),
SHA-256 c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4.
The pinned tree contains no NOTICE path or applicable NOTICE chain.

The attributed port keeps the symplectic-basis predicate and a single existence
construction. Plane extraction, nondegenerate restriction to the plane and its
orthogonal complement, and strong induction on dimension carry the proof.
The auxiliary induction and index equivalence are local to the existence proof;
pairing projections, coordinate sum formulas and the even-dimension corollary
are not separate ported declarations. This is an existing attributed result.
Retire the port when this repository's changed Mathlib pin provides an equivalent
declaration, replacing consumers by direct applications of that declaration.

For the predictive symplectic completion, the supplier applies separately to the
symplectic form restricted to the actual visible image im(J O-transpose) and the
hidden kernel of O, after nondegeneracy of these restrictions has been established.
The basis convention has B(p_i,q_i)=+1; Mathlib's Matrix.J has the opposite sign.
The supplier alone does not prove that these spaces are complementary, that the
mixed S-energy vanishes, or that their positive energies have Williamson frequency
blocks. Those are separate obligations, with O representing the whole predictive
closure. Hilbert-space, graph-domain, metaplectic and Gibbs consequences require
further results beyond finite-dimensional basis existence.
