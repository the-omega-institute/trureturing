---
slug: bhardwaj-et-al-2026-question-5-8
bibkey: bhardwajetal2026negativeonemultiplicity
doi: 10.48550/arXiv.2607.08480
url: https://arxiv.org/abs/2607.08480v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.result
---

# A clique corona refutes Bhardwaj et al., Question 5.8

## Problem

Question 5.8 of Bhardwaj, Chau, Ikram, Lather, Nanjangud and Venugopal,
*Multiplicity of negative one of independence polynomials of graphs*, reads:

> Given a connected graph G on n ≥ 2 vertices. Is it true that
> mult₋₁ P_G ≤ ⌈n/2⌉ − 1?

The introduction assumes finite simple graphs. The polynomial has one
term per independent vertex set, with coefficient one for the empty set.
The formal claim quantifies every finite vertex type and every simple graph
on it. Connectivity and order at least two are explicit hypotheses. Lean
takes the ceiling of an exact rational quotient and compares integers.
[arXiv:2607.08480v1, pp. 1–2 and 16](https://arxiv.org/pdf/2607.08480v1#page=16)

## Motivation

This Tier 1 question asks whether the lower bound for the set of
realizable pairs in Theorem 5.7 describes the entire set for every graph
order. The counterexample was preregistered with its source, scope and
success criteria. [#34354](https://github.com/the-omega-institute/trureturing/issues/34354)

## Gap

The preregistration records an exact-title arXiv search, an OpenAlex
search for the question number and polynomial term, and a check of the
indexed citing record. It reports no answer to Question 5.8 within that
scope. It identifies a different question from the same paper in #26718.
Gutman's general corona identity is published and stated in Levit and
Mandrescu's Theorem 1.2. The application to Question 5.8 settles the
specific proposed bound. [#34354](https://github.com/the-omega-institute/trureturing/issues/34354) · [Levit and Mandrescu, Theorem 1.2](https://arxiv.org/pdf/1303.2564v1#page=3)

## Route

Take a clique of t centers and attach k private leaves to each center.
The proof reuses the frozen independence polynomial and deletion identity.
If the independent set contains no center, all tk leaves are free.
If it contains a center, only the (t−1)k leaves owned by other centers
are free. The polynomial for t > 0 is
$$
(1+X)^{(t-1)k}\bigl((1+X)^k+tX\bigr).
$$
For positive k, the residual factor evaluates to −t at −1. The
multiplicity is exactly (t−1)k. For t positive the centers connect
the whole graph and the order is t + tk.

## Falsifier

For t = k = 3, the graph has order 12 and is connected. Its polynomial
is $(1+X)^6((1+X)^3+3X)$, so the multiplicity is 6. The proposed upper
bound is 5. This yields the closed Lean theorem `result : Not Conjecture58`.

## Evidence

The Lean result uses the actual independent-set partition and symbolic
multiplicity lemmas. The witness order, connectivity, multiplicity and
exact bound are all used in the contradiction. An independent enumeration
over all 4,096 subsets counted 704 independent sets. Its shifted
polynomial is $P(Y-1)=-3Y^6+3Y^7+Y^9$.

## Triage

- **Proved in Lean.** The corona on three centers with three leaves apiece
  is a counterexample. The kernel also checks connectivity for positive t,
  the factorization for positive t, and the exact multiplicity for
  positive t and k.
- **Algebraic consequences of the checked formulas.** With t = 3 every
  k ≥ 3 gives a counterexample. With k = t−1 and t ≥ 2 the ratio of
  multiplicity to order is $(t-1)^2/t^2$ and tends to 1. Consequently,
  a universal bound with leading term $cn$ for a fixed $c<1$ and a bounded
  additive term cannot hold for all connected graphs. The same family has
  independence number tk because all leaves can be selected and choosing
  a center yields at most $1+(t-1)k\le tk$. It gives the realizable pair
  (6, 9) at order 12, outside Theorem 5.7's lower-bound set. These
  consequences are elementary deductions recorded in this dossier.
- **Source scope.** Theorem 5.7 supplies a lower bound and its proposed
  equality fails. The witness has independence number 9 at order 12,
  so the separate boundary statement in Theorem 5.9 for independence
  number n−2 still applies within its stated scope. Lemma 4.7 concerns
  one leaf per center and is consistent with the specialization k = 1.
- **Open here.** The full set of realizable pairs and sharp finite-order
  upper bounds beyond the proved source ranges remain open in this dossier.

## ASSUMED-UNVERIFIED

The literature census has the scope reported in #34354. The Lean check
establishes the mathematical negation, and source fidelity was separately
checked against the published text. Worldwide priority and a minimum
counterexample order are unverified.
