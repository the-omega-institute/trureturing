---
bibkey: goodearlpardowehrung2004semilattices
authors: K. R. Goodearl; E. Pardo; F. Wehrung
year: 2004
title: "Semilattices of Groups and Inductive Limits of Cuntz Algebras"
doi: null
url: https://arxiv.org/pdf/math/0408072v1
claim: "Lemma 2.1 constructs the unique idempotent component identity for regular abelian monoids; Theorem 3.2 characterizes refinement by a distributive idempotent semilattice and two Mayer–Vietoris properties."
strata_touched:
  - D5/S3/Combinatorics/Transportation/RegularMayerVietoris
license: citation-only
triage: anchor
---

# Semilattices of groups and inductive limits of Cuntz algebras

K. R. Goodearl, E. Pardo, and F. Wehrung, *Semilattices of Groups and Inductive Limits of Cuntz Algebras*, arXiv:math/0408072v1, Section 2, Lemma 2.1, and Section 3, Theorem 3.2. The source PDF is <https://arxiv.org/pdf/math/0408072v1>.

The source works with abelian additive monoids. Its regularity condition is
`∀ x, ∃ y, x + y + x = x`. For an idempotent `e`, the component is
`X(e) = {x | e ≤ x ∧ x ≤ e}`, where `x ≤ y` means that there is an additive
difference from `x` to `y`. Lemma 2.1 constructs a group with identity `e`
inside each component, proves that every regular element belongs to one such
component, and proves uniqueness of the idempotent identity. The identity is
an idempotent of the original monoid and need not be the global additive zero.

The repository formalization in
`OmegaMath.Algebra.Refinement.RegularComponents` proves idempotent
antisymmetry, component coverage and uniqueness, addition, internal inverses,
and the offset and absorption calculations. Global regularity is used for
coverage; the internal inverse construction only needs an idempotent and
mutual algebraic-preorder membership.

`OmegaMath.Algebra.Refinement.RegularMayerVietoris` proves both directions of
Theorem 3.2, using Riesz refinement as the meaning of a distributive idempotent
semilattice. The reverse direction constructs all four entries by correcting
a row decomposition with a common lift and its two component inverses.
The D5 theorem combines that classification with the existing exact
transportation correspondence. Conicality appears only in this final
transportation consequence, which includes empty finite carriers and an
arbitrary label type. Embedding, purity, cancellation, finiteness of the
coefficient monoid, and nontriviality are not assumed.

## Verified locator

Source: https://arxiv.org/pdf/math/0408072v1

Scope: Section 2, Lemma 2.1 (regular abelian monoids as semilattices of groups),
and Section 3, Theorem 3.2 (refinement characterized by a distributive
idempotent semilattice and the Mayer–Vietoris property for a regular abelian monoid).

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/RegularMayerVietoris.regular_mvp_iff_finite_fiber_transport`
- Source: K. R. Goodearl, E. Pardo, and F. Wehrung, arXiv:math/0408072v1, Lemma 2.1 and Theorem 3.2.
