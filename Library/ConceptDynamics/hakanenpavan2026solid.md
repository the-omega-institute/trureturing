---
bibkey: hakanenpavan2026solid
authors: Anni Hakanen and Pavan P D
year: 2026
title: Solid-Resolving Sets on Directed Graphs
doi: null
url: https://arxiv.org/abs/2610.35041v1
claim: Conjecture 3.4 asserts the six tournament solid-metric dimension lower bounds 4, 5, 5, 5, 5, 6 at orders 6, 7, 8, 9, 10, 11.
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase
  - D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles
  - D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal
  - D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/hakanenpavan2026solid -->

# Solid-resolving sets on directed graphs

## Verified locator

Source: https://arxiv.org/abs/2610.35041v1

## Definition 1.1 (page 3)

> Let $D$ be a digraph. A set $S \subseteq V(D)$ is a solid-resolving set of $D$ if for every vertex $v \in V(D)$ and every non-empty subset $X \subseteq V(D)$ with $X \neq \{v\}$, there exists $w \in S$ such that $d(w, v) \neq d(w, X)$. The minimum cardinality of a solid-resolving set is called the solid-metric dimension of $D$, and is denoted by $\beta_S(D)$.

Directed distance is shortest directed-path length, or infinity when unreachable.
The Lean encoding takes the infimum of directed walk lengths in `ENat`; removing
cycles preserves the minimum. Distance to a set is the infimum over its members.

## Conjecture 3.4 (page 8)

> We have $\beta_S(\overrightarrow{K_6}) \geq 4$, $\beta_S(\overrightarrow{K_7}) \geq 5$, $ \beta_S(\overrightarrow{K_8}) \geq 5$, $\beta_S(\overrightarrow{K_9}) \geq 5$, $\beta_S(\overrightarrow{K_{10}}) \geq 5$ and $\beta_S(\overrightarrow{K_{11}}) \geq 6$.

The six quantifiers range over every loopless tournament on `Fin n`, including
those which are not strongly connected. The minimum is over all finite solid
sets and exists because the full vertex set is solid. No diameter assumption
is imposed. The auxiliary profile bounds apply to arbitrary ambient order.

## Scope

The source's arbitrary-order minimum and its observation about intermediate
solid-metric dimensions are separate questions. Completeness of the literature
screen in issue #22881 is ASSUMED-UNVERIFIED.
