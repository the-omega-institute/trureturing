---
slug: crew-et-al-2026-dichromatic-monotonicity
bibkey: crew2026dichromatic
doi: 10.48550/arXiv.2611.13273
url: https://arxiv.org/abs/2611.13273v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Coloring/IndependentPartitionExpansion.chromatic_expansion
---

# Crew et al., Conjecture 2

## Problem

For every finite digraph $D$ of order $n$, the ratio $P_D(x)/x^n$ is
nondecreasing for real $x\ge n-1$. For positive integer $k$, $P_D(k)$ counts
the maps from vertices to $k$ colours in which every colour class induces
an acyclic digraph. A pair of opposite arcs forms a directed cycle. At
order one and $x=0$, the formal statement uses the continuous extension,
which is the derivative of $P_D$ at zero. At order zero the ratio is one.
[Conjecture 2](https://arxiv.org/html/2611.13273v1#Thmconj2)

## Motivation

The frozen ordinary chromatic expansion counts colourings by their unlabelled
independent blocks. For digraphs, the corresponding condition is that each
block induces an acyclic subdigraph. This condition is preserved by refinement.

## Gap

The paper's Theorem 7 bounds the evaluations of $P_D$ at $n-1$ and $n$.
The conjecture compares the normalized values at every pair of real arguments
in the closed ray. The sign of each individual partition weight derivative
can vary, so the argument requires control of the sum over acyclic partitions.
[Theorem 7](https://arxiv.org/html/2611.13273v1#Thmthm7)

## Route

Identify the polynomial by counting the injective choices of palette names for
the blocks of an acyclic partition. Express each normalized partition weight
derivative as the incoming transfer sum minus the outgoing transfer sum for
marked singleton splits. The signed subset sum and the beta-moment estimate give
positive transfers for $n\ge2$ and $x\ge n-1$. Summing over acyclic partitions
cancels the internal transfers and leaves nonnegative contributions across
the boundary. Continuity includes the endpoint for orders at least two.
The extended quotient is constant at smaller orders.

## Falsifier

A reversal would give a digraph and $n-1\le a<b$ with $P_D(a)/a^n >
P_D(b)/b^n$, using the stated extension at the removable endpoint. The
original Tier 1 probe restricted its computable witnesses to loopless
digraphs of order at least two and required independent recovery of the
polynomial by direct colour-map counts and interpolation before certifying
a rational reversal by exact comparison.
[Tier 1 preregistration](https://github.com/the-omega-institute/trureturing/issues/31546)

## Evidence

The original Tier 1 preregistration specifies 4,164 labelled loopless
digraphs of orders two through four and 10,000 distinct order-five masks
from $(65537i+31337)\bmod 2^{20}$ for $0\le i<10000$. It specifies exact
comparisons at adjacent points $n-1+i/16$ for $0\le i\le64$ and full-domain
derivative sign checks for orders two through four.
[Original preregistration](https://github.com/the-omega-institute/trureturing/issues/31546)

The colouring bridge `eval_dichromaticPolynomial_nat` identifies the polynomial
by its counts at every natural palette size. The Lean theorem
`normalizedDichromaticPolynomial_monotoneOn` proves the inequality on the
closed real ray. The all-order derivation supplies the transfer argument.
[Colouring bridge](../Blueprint/D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.md)
[Lean theorem and typed resolution](../Blueprint/D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.md)
[All-order derivation](https://github.com/the-omega-institute/trureturing/issues/31546#issuecomment-7022343508)

## Triage

The theorem gives the preregistered weak inequality for every finite order.
Acyclic digraphs have constant normalized value one, and a loop forces
constant normalized value zero. The typed resolution concerns the weak
monotonicity statement.

## ASSUMED-UNVERIFIED

The preregistration records HTTP 429 responses from OpenAlex and Semantic
Scholar. Citation coverage through those services remains unverified.
