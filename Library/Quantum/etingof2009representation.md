---
bibkey: etingof2009representation
authors: Pavel Etingof, Oleg Golberg, Sebastian Hensel, Tiankai Liu, Alex Schwendner, Dmitry Vaintrob, Elena Yudovina
year: 2009
title: Introduction to representation theory
doi: null
url: https://arxiv.org/abs/0901.0827
claim: Over an algebraically closed field, every self-intertwining operator of a finite-dimensional irreducible representation is a scalar.
strata_touched:
  - D5/S3/Quantum/Matrix/RecordSymmetryNoGo
license: citation-only
triage: anchor
---

# Schur's lemma and the triviality of equivariant idempotents

## Verified locator

DOI: none assigned; the canonical locator is the arXiv record:
https://arxiv.org/abs/0901.0827

Retrieved 2026-09-11: the abstract page gives the title above, the seven authors
above, and the identifier arXiv:0901.0827v5 in the primary class math.RT.

The statement this repository depends on is Schur's lemma in the form given in
section 1.3: Proposition 1.16 states that a nonzero intertwining operator
between irreducible representations is an isomorphism, and Corollary 1.17 states
that over an algebraically closed field every self-intertwining operator of a
finite-dimensional irreducible representation is a scalar.

An equivalent statement, phrased directly as the correspondence between
invariant subspaces and equivariant orthogonal projections, appears in
Sophie Morel, MAT 449: Representation theory (2018), section I.3.4,
Theorem I.3.4.1 and Lemma I.3.4.3, printed pages 25 to 26.

## Scope of the dependency

The repository module derives from this only the corollary that an equivariant
idempotent in an irreducible representation is zero or one, and the converse
that a nontrivial such idempotent witnesses reducibility. No claim of a new
proof of Schur's lemma is made, and no priority claim is made about the earliest
appearance of the equivalence in the literature.

The repository module states its hypotheses over the complex matrices with
self-adjointness. Under algebraic irreducibility the zero-or-one conclusion does
not require unitarity, self-adjointness, the complex field, or finite
dimensionality; those hypotheses are therefore stronger than necessary and their
removal would not make the statement new.
