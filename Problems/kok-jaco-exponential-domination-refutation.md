---
slug: kok-jaco-exponential-domination-refutation
bibkey: kok2025jaco
doi: 10.48550/arXiv.2507.16500
triage: theorem
motivation_gids:
  - D5/S0/Certificates/JacoExponentialDominationRefutation
---

# Refutation of Kok's A000149 domination clause

## Problem

Kok, arXiv:2507.16500v1, section 2.3, Conjecture 2.12, printed page 9,
states these two clauses verbatim:

> The vertex subscripts of a γ-set X = ”{v1 }” ∪ {v2 , v7 , v20 , v54 , . . . } of the infinite linear Jaco graph J∞ (x) is given by the sequence A000149: a(t) = ⌊e^t⌋, t = 0, 1, 2, . . . where e ≈ 2.71828 is the Euler number (or Napier’s constant).

> Furthermore, it implies that sequence A000149 is p-graphical where p(G) = {i : j the subscript of vj ∈ X with X some γ-set of G} and F = {G : G = Jn(x), n = 1, 2, 3, . . . }.

The formal target is only the domination clause implied by the first quotation.
A gamma-set is a minimum dominating set, so a failure of domination refutes
the gamma-set assertion. Gamma-set minimality and the separate p-graphical
clause are not encoded.

## Motivation

The paper presents the two-clause statement as a conjecture and leaves its
conjectures for future work. A certified vertex missed by all A000149-indexed
vertices resolves the domination clause and therefore the gamma-set assertion,
while leaving the p-graphical clause untouched.

## Gap

The arXiv version history, the OEIS A000149 entry, and the following named
searches from issue 7316 were checked on 2026-09-12: `"2507.16500" proof`,
`"Integer sequences with conjectured relation"`, `"Jaco graphs" "Euler"`,
`"Jaco" "Conjecture 2.12"`, `"Jaco" "2.12" "counterexample"`, and
`"Jaco graphs" "domination" "2026"`. A proof or refutation was not found in
the checked surfaces. Kok's earlier *Research note: Domination of exact
deg-centric Jaco graphs* supplies background but does not settle this
domination assertion. This is a bounded search report and makes no claim of
exhaustive coverage or first-publication priority.

## Route

For each positive vertex `n`, let `jacoRight n = 2n - d_n`, where `d_n`
counts earlier positive vertices whose right endpoints reach `n`. Prefix
preservation in the recursively constructed endpoint table gives
`d_(n+1) <= d_n + 1`; hence `jacoRight n + 1 <= jacoRight (n+1)`. Iteration
then bounds every endpoint below index 55 by `jacoRight 54 = 87`.

The certified exponential estimates `e^4 < 55` and `144 < e^5` split every
A000149 term into an index at most 54 or at least 144. Vertex 88 is not an
A000149 term. A selected index below 88 has right endpoint at most 87, while a
selected index above 88 is at least 144 and lies beyond `jacoRight 88 = 143`.
Thus no selected vertex is adjacent to 88.

## Falsifier

The counterexample is vertex 88. A correction showing that 88 belongs to
A000149, that some selected index at most 54 has right endpoint at least 88,
that some selected index at least 144 is at most the right endpoint of vertex
88, or that the encoded endpoint recurrence differs from the source graph
would invalidate the proposed refutation.

## Evidence

- Lean module: `D5/S0/Certificates/JacoExponentialDominationRefutation.lean`.
- Structural theorem: `jacoRight_succ_ge : forall n, jacoRight n + 1 <=
  jacoRight (n + 1)`.
- Resolution theorem: `result : not dominationClause`; the `Refuted`
  resolution claim is attached only to this theorem.
- Kernel evaluations: `jacoRight 54 = 87` and `jacoRight 88 = 143`.
- Axiom closure: `propext`, `Classical.choice`, and `Quot.sound` for
  `jacoRight_succ_ge`, `dominationClause`, and `result`.
- The result refutes the necessary domination clause and therefore the
  gamma-set assertion. It proves no statement about gamma-set minimality or
  the separate p-graphical clause.

## Triage

`theorem`. The universal domination clause is refuted by one certified missed
vertex. The second p-graphical clause remains a source boundary and receives no
resolution claim here.

## ASSUMED-UNVERIFIED

The identification of the paper's infinite linear Jaco graph and gamma-set
terminology with the encoded recurrence and domination predicate rests on a
source reading, not a kernel proof. Literature coverage and publication
priority are not kernel-checked; the bounded searches listed above found no
resolution in the checked surfaces. The minimality and p-graphical clauses are
not formalized.
