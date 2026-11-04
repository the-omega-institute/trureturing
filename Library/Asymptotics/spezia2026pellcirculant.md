---
bibkey: spezia2026pellcirculant
authors: Stefano Spezia
year: 2026
title: "OEIS A392131 and A392132: Pell circulant determinant and permanent"
doi: null
url: https://oeis.org/A392131/internal
claim: "Conjecture: lim_{n->oo} A392132(n)/a(n) = 1."
strata_touched:
  - D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio
license: citation-only
triage: anchor
---

# Pell circulant permanent and determinant

## Verified locator

Source: https://oeis.org/A392131/internal

Counterpart: https://oeis.org/A392132/internal

Pell sequence: https://oeis.org/A000129/internal

The source is an OEIS record without pagination or an arXiv identifier. A392131 revision 16
and A392132 revision 10 contain the following sentences in NAME, COMMENT and FORMULA.
The entries were submitted on 31 December 2025 and published on 2 January 2026.

## Source statements

A392131 NAME:

> a(n) is the determinant of the n X n circulant matrix whose rows are formed by successively rotating the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.

A392131 COMMENT:

> a(n) is the determinant of the n X n Toeplitz matrix whose first column is formed by the vector(A000129(n-1), A000129(n-2), ..., A000129(0)) and whose first row is obtained by rotating once the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.

A392131 FORMULA:

> Conjecture: lim_{n->oo} A392132(n)/a(n) = 1.

A392132 NAME:

> a(n) is the permanent of the n X n circulant matrix whose rows are formed by successively rotating the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.

A392132 FORMULA:

> Conjecture: lim_{n->oo} a(n)/A392131(n) = 1.

A000129 NAME:

> Pell numbers: a(0) = 0, a(1) = 1; for n > 1, a(n) = 2*a(n-1) + a(n-2).

## Mathematical encoding

The initial rotation in the COMMENT and EXAMPLE makes the first row
`(P(n-1), P(0), ..., P(n-2))`. Rows and columns are indexed by `Fin n`.
Mathlib's circulant entry is `v(i-j)` with subtraction in `Fin n`, so the vector
`k ↦ (P(n-1-k.val) : ℝ)` gives this row and its successive right rotations.
The Pell numbers are reused from `D5.S1.Recurrence.PellCompanionGcd.P`.
A392131 is the signed determinant, with no absolute value; A392132 is the permanent.
Both empty-matrix values are one, and the limit quantifies over the tail `n ≥ 2`.
The four-by-four source example has first row `(5, 0, 1, 2)` and determinant 640.

The epsilon formulation quantifies over every real positive error and supplies an integer
threshold at least two. It asserts convergence of the actual ratio, without any free
matrix-family parameter. Pell growth bounds the off-diagonal entries of the normalized
matrix by `(6/5)/(12/5)^d`. Positive modular displacements of a closed cycle sum to a
positive multiple of `n`; encoding cycles by a root and a positive composition gives a
vanishing total cycle weight. The permanent and the signed determinant of the normalized
matrix each tend to one.

## Evidence and limits

The source-fidelity experiment is in `the-omega-institute/trureturing-experiments`, commit
`0938258013ceeef91cdfa39de81dad341e6755cf`, at `docs/reports/spezia-pellcirc/check.py`.
Its SHA-256 is `d15fb92594c83cd80aa1092ad28bcfa4fa4963b61867dfc46f05398b2fd9a32c`.
The recorded command `python3 docs/reports/spezia-pellcirc/check.py` exited 0 and printed
`ALL_CHECKS_OK`. It compares the source terms through index 13, exact matrix calculations
through size 16, and cycles through size 8. These finite checks support the encoding;
they do not prove the limit.

The literature screen in issue #21886 found no prior settlement in its searched scope.
Exhaustive literature and citation closure remain ASSUMED-UNVERIFIED. The fixed-constant
cycle estimate also applies to nonnegative matrices satisfying the same entry majorant;
unit diagonal is used for the permanent comparison. A parameterized estimate, sharp
asymptotic constants, positivity of every finite determinant, and other recurrence
families remain open here.
