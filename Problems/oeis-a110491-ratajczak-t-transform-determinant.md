---
slug: oeis-a110491-ratajczak-t-transform-determinant
bibkey: ratajczak2021a110491
doi: null
url: https://oeis.org/A110491
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant
---

# Ratajczak's A110491 T-transform determinant conjecture

## Problem

Lechoslaw Ratajczak's August 4, 2021 COMMENT on OEIS A110491 states:

> Conjecture: {a(n-1), n>=1} is the T-transform of A093178, where T maps a sequence {b(n), n>=1} to the sequence {c(n)} defined by c(n) = det(M_n), where M_n is the n X n matrix with elements M_n(i,j) = b(2*j) for i>j and M_n(i,j) = b(i+j-1) for i<=j.

Here A093178 is `b(r)=1` when `r` is even and `b(r)=r` when `r` is odd.
The matrix indices `i,j` in the comment are one-based. Independently, define
the integer sequence `a` by `a(0)=1`, `a(1)=2`, and

`a(m+2)=2*a(m+1)+4*(m+1)*m*a(m)`.

For zero-based finite indices set `i1=i+1` and `j1=j+1`, and define the
order-`n` integer matrix by the literal source branches

`M_n(i,j)=b(2*j1)` if `i1>j1`, and
`M_n(i,j)=b(i1+j1-1)` if `i1<=j1`.

The resolved statement is the unbounded assertion

```lean
theorem result (m : ℕ) :
    (sourceMatrix (m + 1)).det = sourceA m
```

for every natural `m`. This is exactly the source conjecture at every
positive order, not a finite prefix, a surrogate matrix, a definition of
`a` by determinants, or a consequence of an assumed generating function.

## Motivation

The conjecture identifies a determinant transform of one independently
specified OEIS sequence with another sequence at all orders. Its matrix has
a constant lower triangle but a parity-dependent upper triangle, so the
identity asks for a structural determinant reduction rather than agreement
of initial terms. The target was preregistered in issue #9591 before the
accepted proof was designated for delivery.

## Gap

The published scalar recurrence does not by itself show that the literal
one-based matrix determinant obeys it. The missing bridge is a sequence of
determinant-preserving row and column operations that exposes a continuant
with the correct order-two recurrence. Simplifying `b(2*j)` in prose without
retaining the source branch would also leave the formal object/source match
under-specified.

The supplied bounded prior-work audit read the 15-page April 19, 2004 author
copy of Plouffe's *A search for a mathematical expression for mass ratios
using a large database 2004*, linked from the author's Articles directory
under the same title cited by OEIS A093178. That inspected copy concerns
mass-ratio numerical expression searches, constant databases, PSLQ, and
Fibonacci and Lucas approximations; it contains no inspected T-transform or
A110491 determinant theorem. The official viXra `1409.0099v1` endpoint
returned HTTP 200 with media type `application/pdf` but a zero-byte body, so
that version was not read and its exact byte identity with the author copy is
`ASSUMED-UNVERIFIED`. The audit is not an exhaustive absence or priority
result.

## Route

Subtract every predecessor row from its successor. The first column becomes
a leading one followed by zeros, so expansion removes it and leaves an
`m`-dimensional matrix whose upper part alternates with index parity and whose
subdiagonal is `-2p`.

Conjugate `H` by the diagonal signs `(-1)^(p+1)`. The signs remove the parity
alternation and expose a factor two in every row, giving `2^m` times the
floor-linear matrix `L`. Subtract each adjacent predecessor column from its
successor to convert `L` into the parity-upper matrix `B`. Then multiply `B`
by `U2`, the identity minus the second-superdiagonal matrix. This distance-two
column operation has `det(U2)=1` and converts `B` into the signed tridiagonal
matrix `T` with diagonal `1`, subdiagonal `p`, and superdiagonal `-p`.

Reverse its indices and expand the sparse first row and column. Its
determinants satisfy
`d(m+2)=d(m+1)+(m+1)*m*d(m)`. The empty and one-dimensional determinants
give `d(0)=d(1)=1`. Multiplying by `2^m` yields exactly the independently
specified recurrence and the base values `sourceA(0)=1`, `sourceA(1)=2`.

The public theorem has `proof_shape: content` because this source-specific
reduction and continuant recurrence are not obtained by instantiating a
pre-existing theorem. Its admitted basis is the preregistered external
open-problem resolution. All other mathematical statements used in the
proof are local terms; the public surface is exactly `sourceB`, `sourceA`,
`sourceMatrix`, and `result`. `utility: none` applies: no declaration is a
bounded enumeration, checker, numeric reduction, or isolated certified
instance.

## Falsifier

Any natural `m` for which the determinant of the literal order-`m+1` matrix
differs from the independently recurrent `sourceA m` would refute the result.
A mismatch caused by zero-based substitution for the source's one-based
indices, replacement of the lower branch by a different expression, or use
of a finite prefix would instead show that a different statement had been
formalized. The theorem excludes the first alternative for the exact formal
definitions; documentary review guards the source identification.

## Evidence

The Lean module
`D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.lean` contains
exactly the four public declarations `sourceB`, `sourceA`, `sourceMatrix`,
and `result`. The canonical report binds `result` to statement ID
`sha256:793a9ab2fc29c750d4c362d61a4aa033698063393d4a27d0de0d26e6de8ee2c9`
and type SHA-256
`a713703aa4944a3cb3b912b63af191ab8d6222e67ffe8e1009759126ac1547c0`.
Its axiom closure is exactly `Classical.choice`, `Quot.sound`, and `propext`.
The current 325-line source has SHA-256
`d4330caf7c6289f794e441e87d0b6bb1e618ac0125ca2a006bc5f08f1484030e`;
its only difference from the independently accepted 326-line source is the
required one-line canonical formatting of the header's `anchors` field.

The result quantifies over every natural `m`. The proof treats the zero- and
one-dimensional continuants explicitly and derives the recurrence for an
arbitrary later order. No numerical table or finite computation appears as a
premise.

## Triage

`theorem`; resolution `proved` for Ratajczak's quoted A110491 COMMENT under
the exact A093178 formula and indexing stated above. The resolution concerns
the all-order determinant identity only. The published scalar recurrence and
source sequence formulas retain their source attribution.

## ASSUMED-UNVERIFIED

The source-to-formal identification and the prior-work boundary remain
documentary judgments rather than kernel statements. The bounded audit read
the 321707-byte author copy (SHA-256
`c2f53b56dc78c89cdcee068d7553939ed0eb170399df96f256fe162f3378586b`),
but the official viXra `1409.0099v1` response had a zero-byte body; exact byte
identity between that unread version and the inspected author copy is
`ASSUMED-UNVERIFIED`. Differently phrased, private, or unindexed prior proofs
were not excluded. No exhaustive literature-search, worldwide-priority, or
authorship claim is made. Canonical admission and Freeze status belong to
generated machine artifacts, not this dossier.
