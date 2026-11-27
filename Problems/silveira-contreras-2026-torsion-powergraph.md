---
slug: silveira-contreras-2026-torsion-powergraph
bibkey: silveiracontreras2026powergraph
doi: 10.48550/arXiv.2611.17525
url: https://arxiv.org/abs/2611.17525v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.result
---

# Torsion does not suffice for connectivity of the proper generalized power graph

## Problem

Danilo Silveira and Yerko Contreras Rojas ask in Problem 4.3 whether the finite-group hypothesis in Theorem 4.2(2) can be replaced by the torsion-group hypothesis. The theorem assumes a cyclic center and concludes that the proper generalized power graph is connected with diameter at most four. [Problem 4.3](https://arxiv.org/html/2611.17525v1#S4.Thmtheorem3) · [Theorem 4.2](https://arxiv.org/html/2611.17525v1#S4.Thmtheorem2)

| Source clause | Lean counterpart |
| --- | --- |
| Torsion group with cyclic center | Every element satisfies `IsOfFinOrder` and `Subgroup.center G` satisfies `IsCyclic` |
| Proper generalized power graph | The vertex subtype excludes the identity. For distinct vertices, either ordered list product of conjugates can give the other vertex, with each conjugate $g^{-1}ag$ |
| Connected with diameter at most four | `SimpleGraph.Connected` and `SimpleGraph.ediam ≤ 4` |
| Negative answer | `result : ¬ claim` refutes the assertion for groups in Lean's `Type`, which contains the explicit counterexample |

## Motivation

The question asks whether the elementwise finite-order property suffices for a connectivity theorem proved under finiteness of the whole group.

## Gap

The source proves the diameter bound under finiteness with cyclic center and under torsion with trivial center. Its disconnected example has noncyclic center. [Theorem 4.2 and Example 4.4](https://arxiv.org/html/2611.17525v1#S4.Thmtheorem2)

## Route

Take the directed limit of iterated regular wreath products by $C_2$ under the one-coordinate embeddings. Every limit element has finite order, and the next-stage shift moves every nonidentity representative. Finite lists of conjugators and their base element lift to one stage, where the lower central series rules out an odd product of conjugates of a nonidentity element equaling the identity.

## Falsifier

In $H\times C_2$, with $H$ the wreath limit, the central involution is isolated in both incident directions. There is a distinct proper vertex coming from the first-stage shift. Thus the graph is disconnected.

The witness $H\times C_2$ lies in Lean's `Type` (universe 0). It is countable because $H$ is a quotient of the disjoint union of the finite stages indexed by $\mathbb N$, and $C_2$ is finite. This witness also refutes the paper's assertion over arbitrary groups.

## Evidence

The Lean theorem proves the literal negation of the affirmative torsion statement. [Lean module](../D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.lean) · [Bibliography](../Library/Combinatorics/silveiracontreras2026powergraph.md) · [#35024](https://github.com/the-omega-institute/trureturing/issues/35024)

## Triage

Named Problem 4.3 in arXiv:2611.17525v1. The counterexample addresses the connectedness conjunct of its proposed extension and therefore refutes the conjunction.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain unverified.
