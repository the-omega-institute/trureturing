---
slug: brown-cameron-2020-irrational-imaginary-independence-root
bibkey: browncameron2020imaginary
doi: 10.1016/j.disc.2020.112113
url: https://arxiv.org/abs/2001.08881v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.result
---

# An irrational purely imaginary independence root

## Problem

Brown and Cameron, *A note on purely imaginary independence roots*,
arXiv:2001.08881v2, Question 2 on printed page 11, ask verbatim:

> Are there graphs with purely imaginary independence roots at bi where b is irrational?

The target is the existence of a natural n, a finite simple graph G on
Fin n, and an irrational real b such that I(G,ib)=0. Here I(G,X) sums
X to the cardinality of S over every actual independent vertex subset S,
including the empty subset once. The question imposes no order,
connectivity, independence-number or modulus restriction.

## Motivation

An exact purely imaginary root with irrational imaginary part is a
stronger incidence requirement than density of independence roots near
points of the imaginary axis. The source's rational imaginary roots and
its separate exclusion of square roots of rationals greater than one do
not settle this existential question.

## Gap

The polynomial must arise from the graph's independent subsets. A scalar
polynomial with the desired factor alone does not supply such a graph.
The construction identifies the complete configuration families and
transports an actual vertex carrier to Fin 128.

## Route

Let A be four disjoint copies of K4. Completely join A, thirty-four
distinct edgeless two-vertex blocks, and K44. Different join blocks are
fully adjacent. Every nonempty independent subset lies in one block,
so the empty subset is counted once in

I(G,X) = (1+4X)^4 + 34(2X+X^2) + 44X
= 1+128X+130X^2+256X^3+256X^4
= (1+2X^2)(1+128X+128X^2).

Take b=1/sqrt(2). Irrationality is preserved by inversion, and (ib)^2=-1/2
annihilates the first factor exactly. The original in-place disjoint-sum
identities and the native relabeling theorem supply the product and
transport steps.

## Falsifier

A missing class of independent subsets, repeated empty subset, invalid
vertex equivalence, or incorrect exact evaluation would invalidate the
witness. Failure of another proposed graph would not refute the
existential question. No polynomial identity is assumed by the result.

## Evidence

The native theorem
`D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.result`
constructs n, G and b without additional mathematical hypotheses.
`D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.native_polynomial`
proves the integer polynomial, degree four, every independent-k-subset
cardinality and the entire zero tail. The graph join identities are
`D5/S3/StatisticalMechanics/HardCore/PartitionJoin.configurations_join`
and `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.partition_join`.

The exact-result Reg source preserves its source-equivalence bridge with
unknown continuation. The configuration and polynomial audit templates
remain unresolved, and partition_join has no registration; their
boundaries are disclosed in
[issue 29574](https://github.com/the-omega-institute/trureturing/issues/29574#issuecomment-6825316055).
Unknown continuation is not an undecidability claim.

## Triage

### What the settlement shows

**Proved** by `IrrationalIndependenceRoot.result`: the full original
Question 2 has an affirmative answer. Its mechanism is confinement of
independent subsets to join blocks and the exact factor 1+2X^2. The
witness has b squared equal to 1/2, outside the source's separate
greater-than-one exclusion.

**Proved** by `PartitionJoin.configurations_join` and `partition_join`:
the configuration and partition identities hold for arbitrary finite
vertex subsets of the two graph domains, and the partition identity
holds at every activity in a commutative ring, including zero. These
identities do not require positive activity or nonempty domains.

**Proved** by `IrrationalIndependenceRoot.native_polynomial`: the counts
are 1, 128, 130, 256 and 256 in cardinalities zero through four, with no
larger independent subset. **Computed** as a scalar cross-check by
`python3 -c 'from math import comb; print([1,16+34*2+44,comb(4,2)*4**2+34,4*4**3,4**4])'`:
the same coefficient vector is obtained. This arithmetic check supplies
no graph-realization or root-existence evidence beyond the native proof.

**Unresolved**: minimum graph order, sharpness of 128, a classification
of irrational imaginary parts, and realization of every irrational
value. The source's separate Question 1 on minimum order is not settled.
The construction does not overturn the source's greater-than-one
exclusion or change its other established results.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive later-literature coverage are
unverified. The bounded arXiv topic and irrational-root searches,
author research page and citing-work metadata inspection found no
prior answer. Metadata and the previously inspected citing texts are
not an exhaustive theorem census.
