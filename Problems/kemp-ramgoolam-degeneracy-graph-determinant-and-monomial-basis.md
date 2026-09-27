---
slug: kemp-ramgoolam-degeneracy-graph-determinant-and-monomial-basis
bibkey: kempramgoolam2026degeneracy
doi: null
url: https://arxiv.org/html/2603.05259v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/DegeneracyGraphDeterminant
  - D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis
---

# Kemp–Ramgoolam arbitrary-depth determinant and monomial-basis conjectures

## Problem

Kemp and Ramgoolam's arXiv:2603.05259v2 defines a layered source tree with recursive threshold sets in (3.1)–(3.4). Its ordinary source columns are the disjoint union in (3.5)–(3.6). The leaf-path matrix is (6.21). The determinant conjecture is the signed sibling-only product (6.22): at the last layer (i=L), the exponent is one, while at every earlier layer (i<L), the exponent is the number of actual source-bounded positive threshold vectors whose literal two-root truncation retains both endpoints, as in (6.23)–(6.27). Labels need only separate siblings; parent-dependent fibers and equal labels under unrelated parents are permitted. The monomial-basis conjecture is the assertion in (3.6) that these ordinary source monomials span the required column space at arbitrary depth.

## Motivation

The source is a named recent open problem whose exact arbitrary-depth clauses are retained as one cohesive target. The five-owner chain follows the source dependency order and keeps determinant, multiplicity, and actual algebra-basis obligations together.

## Route

`D5/S3/Quantum/Algebra/DegeneracyGraphDeterminant` formalizes the complete source tree, recursive thresholds, columns, and `RawM` leaf-path evaluation. `DegeneracyGraphDeterminantRecurrence` supplies the occupied-degree reindexing, pruning square, explicit row/column equivalences, and signed recurrence. `DegeneracyGraphDeterminantMultiplicity` supplies the source-bounded two-root witnesses and their pruning bijections. `DegeneracyGraphDeterminantFactorization.sourceSquare_det_factorization` proves the exact signed factorization. `DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions` constructs the actual basis in arbitrary `A` with `[CommRing A] [Algebra Complex A]`, identifies each basis vector with a literal generator-product monomial, and proves both (2.29) and (2.30) with the stated inverse coefficient.

## Gap

The proof uses sibling injectivity only and does not assume a global grid, uniform fibers, depth one or two, a semisimplicity proxy, or a postulated evaluation equivalence. Neidinger 2019 Theorem 2 and Sauer 2004 Theorem 3.3 are relevant conditional global-grid results, not proofs of this exact parent-dependent tree problem. Werner 1980 and Mühlbach 1988 have closed publisher access in the bounded search and remain unread primary-body gaps. This dossier therefore makes no exhaustive prior-art, priority, or worldwide-absence claim.

## Falsifier

A counterexample satisfying the stated `SourceTree` hypotheses to the signed determinant identity or to the arbitrary-algebra basis/expansion theorem would refute this resolution. A later primary source proving the exact same arbitrary parent-dependent statement would change the provenance assessment, not the Lean statement.

## Evidence

`D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantFactorization.sourceSquare_det_factorization` proves that for every `T : SourceTree (n + 1)` there is an integer sign `eps = 1` or `eps = -1` such that `(SourceSquare T).det = (eps : ℂ) * sourceFactorProduct T`. The product ranges over the actual ordered `SourceSiblingPair`s, and `sourceExponent` is the cardinality of the corresponding `SourcePairTailWitness`; the theorem also states that the exponent at `Fin.last n` (the source layer (i=L)) is one and every source exponent is positive. `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions` proves that for arbitrary `[CommRing A] [Algebra ℂ A]` and `P : Basis (Bottom T) ℂ A` satisfying `CompleteOrthogonalIdempotents`, there is a basis `B : Basis (Columns T) ℂ A` with `B m = sourceMonomial T P m`, the forward expansion `sourceMonomial T P m = ∑ b, RawM T b m • P b`, and the inverse expansion `P b = ∑ m, (SourceSquare T)⁻¹ ((bottomColumnEquiv T).symm m) b • B m`. Both final declarations have the standard `std3` axiom closure.

## Triage

This dossier is a bounded resolution record for the named arXiv source clauses. It does not claim exhaustive prior-art clearance, worldwide priority, or absence of a result in the unread Werner and Mühlbach bodies.

## ASSUMED-UNVERIFIED

Werner 1980 and Mühlbach 1988 primary theorem bodies remain unavailable through the lawful retrieval routes recorded in the bounded literature review. Their relevance to parent-dependent fibers is therefore unresolved.
