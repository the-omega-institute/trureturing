---
slug: li-ganesh-perfect-latin-dimension
bibkey: li2026unbalancedlatin
doi: 10.48550/arXiv.2611.06003
url: https://arxiv.org/abs/2611.06003v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Latin/PerfectBalanceDimension.result
---

# The dimension bound for perfectly balanced Latin rectangles

## Problem

Li and Ganesh, *How Unbalanced Must a Latin Rectangle Be?*, arXiv:2611.06003v1,
Section 10, open problem (5), printed page 17, ask:

> Show directly that a perfectly balanced k×n rectangle needs k≥n/2, using that its coordinate projections are bijections. This would follow from Kusner’s conjecture for ℓ1, a long-standing problem in geometry, but it may be easier for these special point sets.

For positive integers 1 ≤ k ≤ n, a Latin rectangle has k rows, n columns and
symbols 1,…,n, without repetition in a row or column. Let c_i(u) be the column
of symbol u in row i. Define d(u,v)=Σ_i |c_i(u)−c_i(v)| and
I(L)=Σ_{u<v}|d(u,v)−k(n+1)/3|. The target is I(L)=0 ⇒ n≤2k,
for every such rectangle, including n=1.

## Motivation

The target is a necessary dimension bound for this special family of
ℓ1-equilateral point sets. It asks for a direct use of coordinate bijections,
without assuming the general ℓ1 Kusner conjecture. The theorem
`D5/S3/Combinatorics/Latin/PerfectBalanceDimension.result` establishes exactly
this implication for actual Latin rectangles.

## Gap

The preregistration in [issue #27046](https://github.com/the-omega-institute/trureturing/issues/27046)
fixes the full source question and positive-size conventions. Its inherited
bounded readings cover the primary note, Díaz et al. (2017),
Ramaswamy–Szeider (2023), and van Dam–Rennen–Husslage (2009).
No general theorem supplying this exact dimension bound was adopted from
those readings. This is a bounded negative finding, not worldwide novelty
or exhaustive absence of prior proof.

## Route

1. Construct c_i as the inverse of each actual row bijection on Fin n;
   zero-based labels preserve all pair distances.
2. For weights a with Σ_u a(u)=0, expand the ordered distance energy
   E(q)=−Σ_{u,v}a(u)a(v)|q(u)−q(v)| as twice the sum of squared cut sums.
   Every row energy is nonnegative.
3. Choose the first row p and weights a(u)=2p(u)+1−n. Permutation reindexing
   and pinned Mathlib power sums evaluate Σ a² and E(p) exactly.
4. Zero imbalance makes every distinct-pair distance k(n+1)/3. Sum the
   energies over all rows and retain the first nonnegative contribution.
   Exact arithmetic gives n≤2k; the case n=1 is handled separately.

## Falsifier

A legal positive-size Latin rectangle with I(L)=0 and n>2k would refute the
claim. The formal implication excludes every such rectangle, rather than
checking only a finite list of sizes.

## Evidence

The canonical mathematical source is
`D5/S3/Combinatorics/Latin/PerfectBalanceDimension.lean`; its Scribe mirrors
`LatinRectangle`, `positions`, `pairDistance`, `imbalance`, and `result`.
The result statement identity is
`sha256:d3a34b9f5eea0c67340c613ee4ace2978a80a6cf1978c1f726ff62e3e85b7f47`,
with type identity
`sha256:c12f0e07d097f5f6a88e3871bc658cdcf602f99aa93a9085bf4fc9eca81ee402`.
Its axiom closure consists of `Classical.choice`, `Quot.sound`, and `propext`.
Positions are actual inverse row permutations, and distances and imbalance
are rational-valued. The mathematical source is unchanged by publication.

## Triage

`theorem`; the mathematical resolution of the quoted question is `proved`.
`admission_basis: open-problem-resolution` under issue #27046. Every one of
the twelve private theorem helpers and the public result is conservatively
`proof_shape: bind-only`; every private helper has an actual proof consumer.
No escape witness or additional mathematical content is claimed. The argument
is uniform and symbolic, so `utility: none` applies.

The independent strict timed attempt remains
[unresolved](https://github.com/the-omega-institute/trureturing/issues/27046#issuecomment-6672602406),
with its [readout](https://github.com/the-omega-institute/trureturing/issues/27046#issuecomment-6672618344)
unchanged. Mathematical resolution metadata does not resettle that timed event.

The source-owner Reg proof is compiled but its audit is `declared_unresolved`:
`IE-C050 ClosedTruthReadout`, `reason=unclassified_form`,
`rule=source.residual_requires_open`; no certificate is present.
The missing evidence is current validated four-slot binding.
The [§3.9 linked-issue exception](https://github.com/the-omega-institute/trureturing/issues/27046#issuecomment-6672183577)
remains explicit; this is not audit certification.

### What the settlement shows

- Proved by the named result: perfect balance in the stated positive-size
  Latin model forces n≤2k, including n=1.
- Proof mechanism: actual coordinate bijections supply zero-sum weights;
  the nonnegative cut-energy identity turns equal pair distances into the
  dimension obstruction. Column injectivity remains in the formal carrier;
  the estimate uses its row bijections.
- Open here: a separately stated relaxation dropping column injectivity,
  sharpness of this bound, and classification of equality cases. No new
  companion theorem is included in this delivery.
- Open here: the general ℓ1 Kusner conjecture and nonsquare impossibility.
  The present result does not settle the source's other open questions or
  alter its independently established results.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are not established.
The rational-to-real interpretation and one-based-to-zero-based convention
are semantic source correspondences; no separate bridge theorem is delivered.
The strict attempt outcome and the unfinished registration audit retain the
explicit boundaries above. Required CI, final independent review, merge,
and first-dev verification are separate publication obligations.
