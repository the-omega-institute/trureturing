---
slug: gobel-misra-colored-path-determinant-refutation
bibkey: gobel2025colored
doi: 10.48550/arXiv.2506.23936
url: https://arxiv.org/abs/2506.23936v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result
---

# Gobel-Misra Colored-Path Determinant Refutation

## Problem

Gobel and Misra, arXiv:2506.23936v1, Conjecture 5.3, printed page 27,
assert that two colored paths on `m` vertices with equal generic
concentration-matrix determinants are identical, reflections, or instances of
the color configuration in Theorem 3.6 when `m` is even and Theorem 3.8 when
`m` is odd, allowing the listed configuration to be reflected.

The formal `claim` quantifies over the vertex-color type, the edge-color type,
the path length, and both labelled paths. It reads the final reflection clause
in the widest form: neither path, the first path, the second path, or both paths
may be reflected. The repository result is `Not claim`.

## Motivation

The frozen result
`D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result`
gives an exact seven-vertex counterexample to the published universal claim.
It compares the generic determinants in the same multivariable polynomial ring
used to encode the source's vertex and edge color constraints.

## Gap

The bounded prior-resolution screen recorded in issue 8621 checked the arXiv
version record, exact title and identifier searches, arXiv abstract search, and
the two Semantic Scholar citations then available. It disclosed no later proof
or refutation of Conjecture 5.3. Google Scholar was not verified.

## Route

Use one vertex color `a`, two edge colors `u` and `v`, and `m = 7`. Give the
first path edge sequence `(u,v,v,u,u,v)` and the second
`(u,u,v,u,v,v)`. Successive endpoint expansions of their tridiagonal
concentration matrices reduce both determinants to
`a^7-3a^5u^2-3a^5v^2+2a^3u^4+6a^3u^2v^2+2a^3v^4-2au^4v^2-2au^2v^4`.

The two paths are unequal and are not reflections. Since seven is odd, only
the Theorem 3.8 branch can remain. Each of its four reflection variants fails
an explicit edge-color equality, so none of the conjecture's alternatives
holds.

## Falsifier

An incorrect transcription of Theorem 3.8, a mismatch between the source's
generic concentration matrix and `concentration`, or an error in either exact
determinant expansion would invalidate the refutation. A prior published
resolution of this exact conjecture would invalidate the
`open-problem-resolution` eligibility without changing the formal
counterexample.

## Evidence

The formal carrier and sole public theorem are `claim : Prop` and
`result : Not claim` in
`D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.lean`.
The proof constructs both paths, proves determinant equality by pinned matrix
determinant expansions and ring normalization, and rejects every conclusion
alternative by exact finite evaluation. The matching Scribe theorem node binds
the frozen result to this dossier with `OpenProblemResolutionClaim(Refuted)`.

## Triage

`theorem`; Tier 1 recent named external conjecture, preregistered in issue 8621
before proof implementation. The admission basis is
`open-problem-resolution`; the conservative classification is
`proof_shape: bind-only` with `escape_witness: none`. Its computational use is
a `certified-instance` with a typed `refutes` edge from `result` to `claim`.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded screen cannot
exclude every prior resolution. Source-to-Lean fidelity requires independent
comparison with arXiv:2506.23936v1; the Lean kernel checks the formal statement
and proof, not that prose correspondence. The resolution binding records the
current frozen theorem and does not by itself establish publication or merge.
