---
slug: fernandes-2026-intermediate-group-invariant
bibkey: fernandes2026invariants
doi: 10.48550/arXiv.2609.20516
url: https://arxiv.org/html/2609.20516v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/PowerInvariantRefinement.finite_source_endpoint
---

# A partition strictly between group isomorphism and simultaneous power equivalence

## Problem

Problem 6.2 of Fernandes–Qureshi–Reis–Ribas, arXiv:2609.20516v1, asks
for a partition P on all finite groups with P₁<P<P₂, P₂<P<P₅ or P₅<P<P₆.
The exact wording and definitions are in
[the literature note](../Library/FiniteGroups/fernandes2026invariants.md).
Here P₁ is group isomorphism and P₂ requires one bijection preserving all
integer powers simultaneously. The strict order is finer-to-coarser.

## Motivation

The first interval asks whether simultaneous power maps forget group
information that can be restored partially without recovering isomorphism.
Agreement on abelianity restores one such invariant.

## Gap

The source supplies power-equivalent abelian and nonabelian groups.
A strict intermediate partition additionally needs nonisomorphic groups
that the added invariant still identifies. Two nonabelian central extensions
with distinct center orders provide this second pair.

## Route

Define R(G,H) to be simultaneous power equivalence and agreement on
abelianity. Identity, inverse and composition prove equivalence; group
isomorphisms preserve both conditions. On F₃⁵ let T(u,v) have product
(x,z)(y,w)=(x+y,z+w+u(a b′−b a′)+v(c d′−d c′)).
T(0,0) is abelian and T(1,0) is not. T(1,0) and T(1,1) are both
nonabelian, with centers of orders 27 and 3. The coordinate bijection
preserves every integer power. The two pairs establish both strictnesses.
The relation is defined on all finite groups, including the trivial group.

## Falsifier

A failure of the single-bijection quantifier, the actual group laws, the
center calculations or either strictness pair would break this argument.
A cardinality-only relation would not establish the source endpoint.

## Evidence

The native module is `D5/S3/FiniteGroups/PowerInvariantRefinement.lean`.
`finite_source_endpoint` states equivalence and both strict refinements on
a bundle with actual Group and Finite carriers. `isomorphism_invariant`
explicitly transports R in both arguments. The strictness proof uses
actual centers and group isomorphisms, rather than numerical proxies.
The linked Scribe owns the native declaration binding.

## Triage

This is the first alternative of the literal disjunctive Problem 6.2.
The common refinement, prime-exponent power phenomenon and central
extensions are classical ingredients. Neither the other intervals nor
another numbered problem is claimed.

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of the current correction/solution
search are unverified. This elementary combination is not claimed as an
original group construction. Repository integration and external review
are separate from the mathematical statement.
