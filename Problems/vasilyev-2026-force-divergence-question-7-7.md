---
slug: vasilyev-2026-force-divergence-question-7-7
bibkey: vasilyev2026upordown
doi: null
url: https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result
---

# Vasilyev's Question 7.7 on force-divergence

## Problem

Oleg Vasilyev, *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*, Question 7.7, arXiv:2611.20344v2, §7, page 33.

> Does every force-divergent set, that is, every $A$ such that $T_S$ is unbounded for all $S \supseteq A$, contain a tail of a chain?

Let $P$ be the positive integers. For $S\subseteq P$, the map $T_S$ applies $U(x)=\lceil 3x/2\rceil$ on $S$ and $D(x)=\lceil x/2\rceil$ elsewhere. Section 1.1 calls $T_S$ unbounded if some positive starting vertex has an orbit that never enters a periodic cycle. Section 3.2 gives the tail from $y$ as the entire set of up iterates $U^k(y)$ for $k\ge0$, including $y$. Question 7.7 quantifies over every $A\subseteq P$ and every $S$ between $A$ and $P$. [Published question](https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7) · [Exact Tier 1 preregistration](https://github.com/the-omega-institute/trureturing/issues/32194)

## Motivation

Proposition 3.3(a) identifies sets containing a chain tail with sets whose map has a strictly increasing orbit. Such a tail persists in every superset, so its existence implies force-divergence. Question 7.7 asks for the reverse implication. [Proposition 3.3(a)](https://arxiv.org/html/2611.20344v2#S3.Thmtheorem3)

## Gap

Force-divergence allows an up step to follow a down step. For the reverse implication to fail, the omitted vertices must meet every all-up tail while still allowing growth each time a superset directs an orbit down.

## Route

Let $b_0=3$ and $b_{n+1}=U^{2b_n}(n+1)$. Use $A=P\setminus\{b_{n+1}:n\ge0\}$. The iterate defining $b_{n+1}$ hits an omitted vertex from $n+1$. Each up step increases a positive integer by at least one, so $b_{n+1}>2b_n$. If $m=b_{n+1}$, the rounding bounds give
$$b_n<D(m)<U(D(m))<m.$$
Both intermediate vertices lie in $A$. For every $S\supseteq A$, a positive vertex in $S$ grows in one step. A positive vertex outside $S$ is omitted and its next three steps are down, up, up, giving an endpoint at least $9m/8>m$. Induction on the number of blocks yields arbitrarily large values in the orbit of every positive start.

## Falsifier

A mismatch in the positive-state maps, the quantification over supersets, eventual periodicity, or the inclusion of time zero in a tail would invalidate the correspondence. For the construction, an omitted intermediate vertex or a non-increasing block endpoint would invalidate the growth argument.

## Evidence

The settling declaration is `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result`. Lean checks the single symbolic witness in both branches under the pinned Mathlib imports. The exact source bridge identifies natural division with the ceiling maps on the positive subtype, transports the quantifier over all supersets, and equates entry into `Function.periodicPts` with a positive-period repeat. It also transports the full all-up tail and checks Proposition 3.3(a) from time zero. The checked axiom closure is `propext`, `Classical.choice` and `Quot.sound`. [Accepted mathematical evidence](https://github.com/the-omega-institute/trureturing/issues/32194#issuecomment-7037550381)

## Triage

### What the settlement shows

The reverse implication is refuted by the settling declaration. In the construction, all positive starts have unbounded orbit values for every positive superset of the witness, even though the witness contains no chain tail. The forward implication from a chain tail to force-divergence still follows from Proposition 3.3(a). Section 6.5 already uses down-up-up growth for a residue-class example. The spaced omission construction ensures that both intermediate vertices belong to $A$ at every omitted vertex and that every tail encounters an omission. [Section 6.5](https://arxiv.org/html/2611.20344v2#S6.SS5)

## ASSUMED-UNVERIFIED

The preregistration and independent source review found no earlier exact settlement in the material they checked. Exhaustive literature completeness remains unverified. The broader OpenAlex phrase query returned HTTP 429 during that review.
